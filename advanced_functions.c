#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <limits.h>
#include <linux/input.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/reboot.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#include <sys/wait.h>
#include <sys/limits.h>
#include <dirent.h>
#include <sys/stat.h>

// statfs
#include <sys/vfs.h>

#include <signal.h>
#include <sys/wait.h>

#include "bootloader.h"
#include "common.h"
#include "cutils/properties.h"
#include "firmware.h"
#include "install.h"
#include "make_ext4fs.h"
#include "minui/minui.h"
#include "minzip/DirUtil.h"
#include "roots.h"
#include "recovery_ui.h"

#include "extendedcommands.h"
#include "advanced_functions.h"
#include "nandroid.h"
#include "mounts.h"
#include "flashutils/flashutils.h"
#include "edify/expr.h"
#include <libgen.h>
#include "mtdutils/mtdutils.h"
#include "bmlutils/bmlutils.h"
#include "cutils/android_reboot.h"


/*****************************************/
/*   DO NOT REMOVE THIS CREDITS HEARDER  */
/* IF YOU MODIFY ANY PART OF THIS SOURCE */
/*  YOU MUST AGREE TO SHARE THE CHANGES  */
/*                                       */
/*       Start PhilZ Menu settings       */
/*      Code written by PhilZ@xda        */
/*      Part of PhilZ Touch Recovery     */
/*****************************************/

// redefined MENU_MAX_COLS from ui.c - Keep same value as ui.c until a better implementation.
// used to format toggle menus to device screen width (only touch build)
#define MENU_MAX_COLS 64

// Returns the current time in msec: 
unsigned long gettime_now_msec(void) {
    struct timeval now;
    long mseconds;
    gettimeofday(&now, NULL);
    mseconds = now.tv_sec * 1000;
    mseconds += now.tv_usec / 1000;
    return mseconds;
}

//start print tail from custom log file
void ui_print_custom_logtail(const char* filename, int nb_lines) {
    char * backup_log;
    char tmp[PATH_MAX];
    FILE * f;
    int line=0;
    sprintf(tmp, "tail -n %d %s > /tmp/custom_tail.log", nb_lines, filename);
    __system(tmp);
    f = fopen("/tmp/custom_tail.log", "rb");
    if (f != NULL) {
        while (line < nb_lines) {
            backup_log = fgets(tmp, PATH_MAX, f);
            if (backup_log == NULL) break;
            ui_print("%s", tmp);
            line++;
        }
        fclose(f);
    } else
        LOGE("Cannot open /tmp/custom_tail.log\n");
}

// is there a second storage (/sdcard is always present in fstab)
int has_second_storage() {
    return (volume_for_path("/external_sd") != NULL
                || volume_for_path("/emmc") != NULL);
}

// delete a file
void delete_a_file(const char* filename) {
    ensure_path_mounted(filename);
    remove(filename);
}

// check if file or folder exists
int file_found(const char* filename) {
    struct stat s;
    if (strncmp(filename, "/sbin/", 6) != 0 && strncmp(filename, "/res/", 5) != 0 &&
            strncmp(filename, "/tmp/", 5) != 0) {
        // do not try to mount ramdisk, else it will error "unknown volume for path..."
        ensure_path_mounted(filename);
    }
    if (0 == stat(filename, &s))
        return 1;

    return 0;
}

// check directory exists
int directory_found(const char* dir) {
    struct stat s;
    ensure_path_mounted(dir);
    lstat(dir, &s);
    if (S_ISDIR(s.st_mode))
        return 1;

    return 0;
}

//check if path is in ramdisk since volume_for_path() will be NULL on these
int is_path_ramdisk(const char* path) {
    const char *ramdisk_dirs[] = { "/sbin/", "/res/", "/tmp/", NULL };
    int i = 0;
    while (ramdisk_dirs[i] != NULL) {
        if (strncmp(path, ramdisk_dirs[i], strlen(ramdisk_dirs[i])) == 0)
            return 1;
        i++;
    }
    return 0;
}

//copy file (ramdisk check compatible)
int copy_a_file(const char* file_in, const char* file_out) {
    if (strcmp(file_in, file_out) == 0) {
        LOGI("source and destination files are same, skipping copy.\n");
        return 0;
    }

    if (!is_path_ramdisk(file_in) && ensure_path_mounted(file_in) != 0) {
        ui_print("cannot mount volume for %s\n", file_in);
        return -1;
    }

    if (!is_path_ramdisk(file_out) && ensure_path_mounted(file_out) != 0) {
        ui_print("无法挂载分区 %s\n", file_out);
        return -1;
    }

    //this will chmod folder to 775
    char tmp[PATH_MAX];
    strcpy(tmp, file_out);
    ensure_directory(dirname(tmp));
    FILE *fp = fopen(file_in, "rb");
    if (fp == NULL) {
        ui_print("找不到源文件 (%s)\n", file_in);
        return -1;
    }
    FILE *fp_out = fopen(file_out, "wb");
    if (fp_out == NULL) {
        ui_print("创建目标文件失败 %s\n", file_out);
        return -1;
    }

    //start copy
    char buf[PATH_MAX];
    size_t size;
    //unsigned int size;
    while (size = fread(buf, 1, sizeof(buf), fp)) {
        fwrite(buf, 1, size, fp_out);
    }
    fclose(fp);
    fclose(fp_out);
    return 0;
}

// get file size (by Dees_Troy - TWRP)
unsigned long Get_File_Size(const char* Path) {
    struct stat st;
    if (stat(Path, &st) != 0)
        return 0;
    return st.st_size;
}

// get partition size info (adapted from Dees_Troy - TWRP)
unsigned long long Total_Size; // Overall size of the partition
unsigned long long Used_Size; // Overall used space
unsigned long long Free_Size; // Overall free space

int Get_Size_Via_statfs(const char* Path) {
    struct statfs st;
    Volume* volume = volume_for_path(Path);
    if (NULL == volume) {
        LOGE("Cannot get size of null volume '%s'\n", Path);
        return -1;
    }
    if (is_data_media_volume_path(volume->mount_point))
        volume = volume_for_path("/data");
    if (volume == NULL || volume->mount_point == NULL || statfs(volume->mount_point, &st) != 0) {
        LOGE("Unable to statfs for size '%s'\n", Path);
        return -1;
    }

    Total_Size = (unsigned long long)(st.f_blocks) * (unsigned long long)(st.f_bsize);
    Free_Size = (unsigned long long)(st.f_bfree) * (unsigned long long)(st.f_bsize);
    Used_Size = Total_Size - Free_Size;
    // LOGI("%s: tot=%llu, use=%llu, free=%llu\n", volume->mount_point, Total_Size, Used_Size, Free_Size); // debug
    return 0;
}

// alternate method for statfs (emmc, mtd...)
int Find_Partition_Size(const char* Path) {
    FILE* fp;
    char line[512];
    char tmpdevice[1024];

    Volume* volume = volume_for_path(Path);
    if (volume != NULL) {
        // In this case, we'll first get the partitions we care about (with labels)
        fp = fopen("/proc/partitions", "rt");
        if (fp != NULL) {
            while (fgets(line, sizeof(line), fp) != NULL)
            {
                unsigned long major, minor, blocks;
                char device[512];
                char tmpString[64];

                if (strlen(line) < 7 || line[0] == 'm')
                    continue;

                sscanf(line + 1, "%lu %lu %lu %s", &major, &minor, &blocks, device);
                sprintf(tmpdevice, "/dev/block/");
                strcat(tmpdevice, device);

                if (volume->device != NULL && strcmp(tmpdevice, volume->device) == 0) {
                    Total_Size = blocks * 1024ULL;
                    //LOGI("%s(%s)=%llu\n", Path, volume->device, Total_Size); // debug
                    fclose(fp);
                    return 0;
                }
                if (volume->device2 != NULL && strcmp(tmpdevice, volume->device2) == 0) {
                    Total_Size = blocks * 1024ULL;
                    fclose(fp);
                    return 0;
                }
            }
            fclose(fp);
        }
    }

    LOGE("Failed to find partition size '%s'\n", Path);
    return -1;
}
//----- End partition size

// get folder size (by Dees_Troy - TWRP)
unsigned long long Get_Folder_Size(const char* Path) {
    DIR* d;
    struct dirent* de;
    struct stat st;
    char path2[PATH_MAX]; char filename[PATH_MAX];
    unsigned long long dusize = 0;
    unsigned long long dutemp = 0;

    // Make a copy of path in case the data in the pointer gets overwritten later
    strcpy(path2, Path);

    d = opendir(path2);
    if (d == NULL)
    {
        LOGE("error opening '%s'\n", path2);
        LOGE("error: %s\n", strerror(errno));
        return 0;
    }

    while ((de = readdir(d)) != NULL)
    {
        if (de->d_type == DT_DIR && strcmp(de->d_name, ".") != 0 && strcmp(de->d_name, "..") != 0)
        {
            strcpy(filename, path2);
            strcat(filename, "/");
            strcat(filename, de->d_name);
            dutemp = Get_Folder_Size(filename);
            dusize += dutemp;
            dutemp = 0;
        }
        else if (de->d_type == DT_REG)
        {
            strcpy(filename, path2);
            strcat(filename, "/");
            strcat(filename, de->d_name);
            stat(filename, &st);
            dusize += (unsigned long long)(st.st_size);
        }
    }
    closedir(d);
    return dusize;
}


/**********************************/
/*       Start file parser        */
/*    Original source by PhilZ    */
/**********************************/
// todo: parse settings file in one pass and make pairs of key:value
// get value of key from a given config file
static int read_config_file(const char* config_file, const char *key, char *value, const char *value_def) {
    int ret = 0;
    char line[PROPERTY_VALUE_MAX];
    ensure_path_mounted(config_file);
    FILE *fp = fopen(config_file, "rb");
    if (fp != NULL) {
        while(fgets(line, sizeof(line), fp) != NULL) {
            if (strstr(line, key) != NULL && strncmp(line, key, strlen(key)) == 0 && line[strlen(key)] == '=') {
                strcpy(value, strstr(line, "=") + 1);
                //remove trailing \n char
                if (value[strlen(value)-1] == '\n')
                    value[strlen(value)-1] = '\0';
                if (value[0] != '\0') {
                    fclose(fp);
                    LOGI("%s=%s\n", key, value);
                    return ret;
                }
            }
        }
        ret = 1;
        fclose(fp);
    } else {
        LOGI("Cannot open %s\n", config_file);
        ret = -1;
    }

    strcpy(value, value_def);
    LOGI("%s set to default (%s)\n", key, value_def);
    return ret;
}

// set value of key in config file
static int write_config_file(const char* config_file, const char* key, const char* value) {
    if (ensure_path_mounted(config_file) != 0) {
        LOGE("Cannot mount path for settings file: %s\n", config_file);
        return -1;
    }

    char config_file_tmp[PATH_MAX];
    strcpy(config_file_tmp, config_file);
    ensure_directory(dirname(config_file_tmp));
    strcpy(config_file_tmp, config_file);
    strcat(config_file_tmp, ".tmp");
    delete_a_file(config_file_tmp);
    FILE *fp = fopen(config_file, "rb");
    FILE *f_tmp = fopen(config_file_tmp, "wb");
    if (f_tmp == NULL) {
        LOGE("failed to create temporary settings file!\n");
        return -1;
    }

    // if a new settings file needs to be created, we write a user info header
    if (fp == NULL) {
        const char* header[] = {
            "#PhilZ Touch Settings File\n",
            "#Edit only in appropriate UNIX format (Notepad+++...)\n",
            "#Entries are in the form of:\n",
            "#key=value\n",
            "#Do not add spaces in between!\n",
            "\n",
            NULL
        };

        int i;
        for(i=0; header[i] != NULL; i++) {
            fwrite(header[i], 1, strlen(header[i]), f_tmp);
        }
    }

    // parsing existing config file and writing new temporary file.
    if (fp != NULL) {
        char line[PROPERTY_VALUE_MAX];
        while(fgets(line, sizeof(line), fp) != NULL) {
            // ignore any existing line with key we want to set
            if (strstr(line, key) != NULL && strncmp(line, key, strlen(key)) == 0 && line[strlen(key)] == '=')
                continue;
            // ensure trailing \n, in case some one got a bad editor...
            if (line[strlen(line)-1] != '\n')
                strcat(line, "\n");
            fwrite(line, 1, strlen(line), f_tmp);
        }
        fclose(fp);
    }

    // write new key=value entry
    char new_entry[PROPERTY_VALUE_MAX];
    sprintf(new_entry, "%s=%s\n", key, value);
    fwrite(new_entry, 1, strlen(new_entry), f_tmp);
    fclose(f_tmp);

    if (rename(config_file_tmp, config_file) !=0) {
        LOGE("failed renaming temporary settings file!\n");
        return -1;
    }
    LOGI("%s was set to %s\n", key, value);
    return 0;
}
//----- end file settings parser

// start wipe data and system options and menu
void wipe_data_menu() {
    static char* headers[] = {  "选择擦除选项",
                                NULL
    };

    char* list[] = { "清空 Data分区/恢复出厂",
                    "一键清空后选择安装刷机包",
                    NULL
    };

    int chosen_item = get_menu_selection(headers, list, 0, 0);
    switch (chosen_item)
    {
        case 0:
            wipe_data(1);
            break;
        case 1:
            //clean for new ROM: formats /data, /datadata, /cache, /system, /preload, /sd-ext, .android_secure
            if (confirm_selection("清空 data, system 以及 preload分区？", "是 - 确定清空!")) {
                wipe_data(0);
                ui_print("-- 正在清除 system...\n");
                erase_volume("/system");
                if (volume_for_path("/preload") != NULL) {
                    ui_print("-- 正在清除 preload...\n");
                    erase_volume("/preload");
                }
                ui_print("现在你可以选择安装新的刷机包了!\n");
            }
            break;
    }
}


/*****************************************/
/*      Start Multi-Flash Zip code       */
/*      Original code by PhilZ @xda      */
/*****************************************/
#define MULTI_ZIP_FOLDER "clockworkmod/multi_flash"
void show_multi_flash_menu() {
    static char* headers_dir[] = { "选择多个ZIP刷机文件",
                                   NULL
    };
    static char* headers[] = {  "选择ZIP刷机文件安装...",
                                NULL
    };

    //browse sdcards until a valid multi_flash folder is found
    char *other_sd = NULL;
    if (volume_for_path("/emmc") != NULL)
        other_sd = "/emmc";
    else if (volume_for_path("/external_sd") != NULL)
        other_sd = "/external_sd";
    
    char tmp[PATH_MAX];
    char* zip_folder = NULL;

    //look for MULTI_ZIP_FOLDER in /sdcard
    struct stat st;
    ensure_path_mounted("/sdcard");
    sprintf(tmp, "/sdcard/%s/", MULTI_ZIP_FOLDER);
    stat(tmp, &st);
    if (S_ISDIR(st.st_mode)) {
        zip_folder = choose_file_menu(tmp, NULL, headers_dir);
        // zip_folder = NULL if no subfolders found or user chose Go Back
        if (no_files_found) {
            ui_print("至少确保有一个文件夹下有ZIP文件 %s\n", tmp);
            ui_print("查找其他文件夹...\n");
        }
    } else
        LOGI("%s 未找到. 搜索其他文件夹...\n", tmp);

    // case MULTI_ZIP_FOLDER not found, or no subfolders or user selected Go Back:
    // search for MULTI_ZIP_FOLDER in other_sd
    struct stat s;
    if (other_sd != NULL) {
        ensure_path_mounted(other_sd);
        sprintf(tmp, "%s/%s/", other_sd, MULTI_ZIP_FOLDER);
        stat(tmp, &s);
        if (zip_folder == NULL && S_ISDIR(s.st_mode)) {
            zip_folder = choose_file_menu(tmp, NULL, headers_dir);
            if (no_files_found)
                ui_print("至少确保有一个文件夹下有ZIP文件 %s\n", tmp);
        }
    }

    // either MULTI_ZIP_FOLDER path not found (ui_print help)
    // or it was found but no subfolder (ui_print help above in no_files_found)
    // or user chose Go Back every time: return silently
    if (zip_folder == NULL) {
        if (!(S_ISDIR(st.st_mode)) && !(S_ISDIR(s.st_mode)))
            ui_print("请将ZIP文件放入文件夹目录 %s\n", MULTI_ZIP_FOLDER);
        return;
    }

    //gather zip files list
    int dir_len = strlen(zip_folder);
    int numFiles = 0;
    char** files = gather_files(zip_folder, ".zip", &numFiles);
    if (numFiles == 0) {
        ui_print("文件夹未找到ZIP文件 %s\n", zip_folder);
    } else {
        // start showing multi-zip menu
        char** list = (char**) malloc((numFiles + 3) * sizeof(char*));
        list[0] = strdup("选择/取消 全选");
        list[1] = strdup(">> 选择需要刷入的ZIP文件 <<");
        list[numFiles+2] = NULL; // Go Back Menu

        int i;
        for(i=2; i < numFiles+2; i++) {
            list[i] = strdup(files[i-2] + dir_len - 4);
            strncpy(list[i], "(x) ", 4);
        }

        int select_all = 1;
        int chosen_item;
        for (;;)
        {
            chosen_item = get_menu_selection(headers, list, 0, 0);
            if (chosen_item == GO_BACK)
                break;
            if (chosen_item == 1)
                break;
            if (chosen_item == 0) {
                // select / unselect all
                select_all ^= 1;
                for(i=2; i < numFiles+2; i++) {
                    if (select_all) strncpy(list[i], "(x)", 3);
                    else strncpy(list[i], "( )", 3);
                }
            } else if (strncmp(list[chosen_item], "( )", 3) == 0) {
                strncpy(list[chosen_item], "(x)", 3);
            } else if (strncmp(list[chosen_item], "(x)", 3) == 0) {
                strncpy(list[chosen_item], "( )", 3);
            }
        }

        //flashing selected zip files
        if (chosen_item == 1) {
            static char confirm[PATH_MAX];
            sprintf(confirm, "Yes - Install from %s", basename(zip_folder));
            if (confirm_selection("确定安装选择的ZIP文件?", confirm))
            {
                for(i=2; i < numFiles+2; i++) {
                    if (strncmp(list[i], "(x)", 3) == 0) {
#ifdef PHILZ_TOUCH_RECOVERY
                        force_wait = -1;
#endif
                        if (install_zip(files[i-2]) != 0)
                            break;
                    }
                }
            }
        }
        free_string_array(list);
    }
    free_string_array(files);
}
//-------- End Multi-Flash Zip code


/*****************************************/
/*   DO NOT REMOVE THIS CREDITS HEARDER  */
/* IF YOU MODIFY ANY PART OF THIS SOURCE */
/*  YOU MUST AGREE TO SHARE THE CHANGES  */
/*                                       */
/*  Start open recovery script support   */
/*  Original code: Dees_Troy  at yahoo   */
/*  Original cwm port by sk8erwitskil    */
/*  Enhanced by PhilZ @xda               */
/*****************************************/

#define SCRIPT_COMMAND_SIZE 512
static int ignore_android_secure = 0;

int check_for_script_file(const char* ors_boot_script) {
    ensure_path_mounted(ors_boot_script);
    struct stat s;
    if (0 != stat(ors_boot_script, &s))
        return -1;

    char tmp[PATH_MAX];
    LOGI("Script file found: '%s'\n", ors_boot_script);
    __system("/sbin/ors-mount.sh");
    // move script file to /tmp
    sprintf(tmp, "mv %s /tmp", ors_boot_script);
    __system(tmp);

    return 0;
}

// sets the default backup volume for ors backup command
static void get_ors_backup_volume(char *other_sd) {
    char value[PROPERTY_VALUE_MAX];
    char value_def[15];

    // favor external storage as default
    if (volume_for_path("/external_sd") != NULL && ensure_path_mounted("/external_sd") == 0)
        sprintf(value_def, "/external_sd");
    else if (volume_for_path("/sdcard") != NULL && ensure_path_mounted("/sdcard") == 0)
        sprintf(value_def, "/sdcard");
    else if (volume_for_path("/emmc") != NULL && ensure_path_mounted("/emmc") == 0)
        sprintf(value_def, "/emmc");
    else
        return;

    read_config_file(PHILZ_SETTINGS_FILE, "ors_backup_path", value, value_def);
    if (strcmp(value, "/external_sd") == 0 || strcmp(value, "/sdcard") == 0 || strcmp(value, "/emmc") == 0) {
        if (volume_for_path(value) != NULL && ensure_path_mounted(value) == 0)
            strcpy(other_sd, value);
    }
}

// checks if ors backup should be done in cwm (ret=0) or twrp (ret=1) format
static int twrp_ors_backup_format() {
    char value[PROPERTY_VALUE_MAX];
    int ret = 0;
    read_config_file(PHILZ_SETTINGS_FILE, "ors_backup_format", value, "cwm");
    if (strcmp(value, "twrp") == 0)
        ret = 1;
    return ret;
}

// Parse backup options in ors
// Stock CWM as of v6.x, doesn't support backup options
static int ors_backup_command(const char* backup_path, const char* options) {
    is_custom_backup = 1;
    int old_compression_value = compression_value;
    compression_value = TAR_FORMAT;
    int old_enable_md5sum = enable_md5sum;
    enable_md5sum = 1;
    backup_boot = 0, backup_recovery = 0, backup_wimax = 0, backup_system = 0;
    backup_preload = 0, backup_data = 0, backup_cache = 0, backup_sdext = 0;
    ignore_android_secure = 1; //disable

    ui_print("设置备份选项:\n");
    char value1[SCRIPT_COMMAND_SIZE];
    int line_len, i;
    strcpy(value1, options);
    line_len = strlen(options);
    for (i=0; i<line_len; i++) {
        if (value1[i] == 'S' || value1[i] == 's') {
            backup_system = 1;
            ui_print("System\n");
            if (nandroid_add_preload) {
                backup_preload = 1;
                ui_print("启用Preload分区备份.\n");
                ui_print("启用将会延长备份时间.\n");
            }
        } else if (value1[i] == 'D' || value1[i] == 'd') {
            backup_data = 1;
            ui_print("Data分区\n");
        } else if (value1[i] == 'C' || value1[i] == 'c') {
            backup_cache = 1;
            ui_print("Cache分区\n");
        } else if (value1[i] == 'R' || value1[i] == 'r') {
            backup_recovery = 1;
            ui_print("Recovery分区\n");
        } else if (value1[i] == '1') {
            ui_print("%s\n", "Option for special1 ignored in CWMR");
        } else if (value1[i] == '2') {
            ui_print("%s\n", "Option for special2 ignored in CWMR");
        } else if (value1[i] == '3') {
            ui_print("%s\n", "Option for special3 ignored in CWMR");
        } else if (value1[i] == 'B' || value1[i] == 'b') {
            backup_boot = 1;
            ui_print("Boot分区\n");
        } else if (value1[i] == 'A' || value1[i] == 'a') {
            ignore_android_secure = 0;
            ui_print("安全模式\n");
        } else if (value1[i] == 'E' || value1[i] == 'e') {
            backup_sdext = 1;
            ui_print("SD-Ext分区\n");
        } else if (value1[i] == 'O' || value1[i] == 'o') {
            compression_value = TAR_GZ_LOW;
            ui_print("备份压缩启用\n");
        } else if (value1[i] == 'M' || value1[i] == 'm') {
            enable_md5sum = 0;
            ui_print("MD5校验关闭\n");
        }
    }

    int ret = -1;
    if (file_found(backup_path)) {
        LOGE("Specified ors backup target '%s' already exists!\n", backup_path);
    } else if (nandroid_get_default_backup_format() != NANDROID_BACKUP_FORMAT_TAR) {
        LOGE("Default backup format must be tar!\n");
    } else if (twrp_backup_mode) {
        ret = twrp_backup(backup_path);
    } else {
        ret = nandroid_backup(backup_path);
    }
    is_custom_backup = 0;
    twrp_backup_mode = 0;
    compression_value = old_compression_value;
    reset_custom_job_settings(0);
    enable_md5sum = old_enable_md5sum;
    return ret;
}

// run ors script code
// this can be started on boot or manually for custom ors
int run_ors_script(const char* ors_script) {
    FILE *fp = fopen(ors_script, "r");
    int ret_val = 0, cindex, line_len, i, remove_nl;
    char script_line[SCRIPT_COMMAND_SIZE], command[SCRIPT_COMMAND_SIZE],
         value[SCRIPT_COMMAND_SIZE], mount[SCRIPT_COMMAND_SIZE],
         value1[SCRIPT_COMMAND_SIZE], value2[SCRIPT_COMMAND_SIZE];
    char *val_start, *tok;

    if (fp != NULL) {
        while (fgets(script_line, SCRIPT_COMMAND_SIZE, fp) != NULL && ret_val == 0) {
            cindex = 0;
            line_len = strlen(script_line);
            if (line_len < 2)
                continue; // there's a blank line or line is too short to contain a command
            LOGI("script line: '%s'\n", script_line); // debug code
            for (i=0; i<line_len; i++) {
                if ((int)script_line[i] == 32) {
                    cindex = i;
                    i = line_len;
                }
            }
            memset(command, 0, sizeof(command));
            memset(value, 0, sizeof(value));
            if ((int)script_line[line_len - 1] == 10)
                remove_nl = 2;
            else
                remove_nl = 1;
            if (cindex != 0) {
                strncpy(command, script_line, cindex);
                LOGI("command is: '%s' and ", command);
                val_start = script_line;
                val_start += cindex + 1;
                strncpy(value, val_start, line_len - cindex - remove_nl);
                LOGI("value is: '%s'\n", value);
            } else {
                strncpy(command, script_line, line_len - remove_nl + 1);
                ui_print("命令: '%s' 没有值\n", command);
            }
            if (strcmp(command, "install") == 0) {
                // Install zip
                ui_print("安装zip文件 '%s'\n", value);
                ensure_path_mounted("/sdcard");
                if (volume_for_path("/external_sd") != NULL)
                    ensure_path_mounted("/external_sd");
                if (volume_for_path("/emmc") != NULL)
                    ensure_path_mounted("/emmc");
                ret_val = install_zip(value);
                if (ret_val != INSTALL_SUCCESS) {
                    LOGE("Error installing zip file '%s'\n", value);
                    ret_val = 1;
                }
            } else if (strcmp(command, "wipe") == 0) {
                // Wipe
                if (strcmp(value, "cache") == 0 || strcmp(value, "/cache") == 0) {
                    ui_print("-- 擦拭缓存分区...\n");
                    erase_volume("/cache");
                    ui_print("-- Cache Partition Wipe Complete!\n");
                } else if (strcmp(value, "dalvik") == 0 || strcmp(value, "dalvick") == 0 || strcmp(value, "dalvikcache") == 0 || strcmp(value, "dalvickcache") == 0) {
                    ui_print("-- 擦拭Dalvik缓存...\n");
                    if (0 != ensure_path_mounted("/data")) {
                        ret_val = 1;
                        break;
                    }
                    ensure_path_mounted("/sd-ext");
                    ensure_path_mounted("/cache");
                    if (no_wipe_confirm) {
                        //do not confirm before wipe for scripts started at boot
                        __system("rm -r /data/dalvik-cache");
                        __system("rm -r /cache/dalvik-cache");
                        __system("rm -r /sd-ext/dalvik-cache");
                        ui_print("已清空Dalvik缓存.\n");
                    } else {
                        if (confirm_selection( "确认擦拭?", "是 - 擦拭Dalvik缓存")) {
                            __system("rm -r /data/dalvik-cache");
                            __system("rm -r /cache/dalvik-cache");
                            __system("rm -r /sd-ext/dalvik-cache");
                            ui_print("已清空Dalvik缓存.\n");
                        }
                    }
                    ensure_path_unmounted("/data");
                    ui_print("-- Dalvik缓存擦拭完成!\n");
                } else if (strcmp(value, "data") == 0 || strcmp(value, "/data") == 0 || strcmp(value, "factory") == 0 || strcmp(value, "factoryreset") == 0) {
                    ui_print("-- 擦拭DATA分区...\n");
                    wipe_data(0);
                    ui_print("-- DATA分区擦拭完成!\n");
                } else {
                    LOGE("Error with wipe command value: '%s'\n", value);
                    ret_val = 1;
                }
            } else if (strcmp(command, "backup") == 0) {
                char other_sd[20] = "";
                // read user set volume target
                get_ors_backup_volume(other_sd);
                if (strcmp(other_sd, "") == 0) {
                    ret_val = 1;
                    LOGE("No valid volume found for ors backup target!\n");
                    continue;
                }

                char backup_path[PATH_MAX];
                // Check if ors backup is set by user to twrp mode
                if (twrp_ors_backup_format())
                    twrp_backup_mode = 1;

                tok = strtok(value, " ");
                strcpy(value1, tok);
                tok = strtok(NULL, " ");
                if (tok != NULL) {
                    // command line has a name for backup folder
                    memset(value2, 0, sizeof(value2));
                    strcpy(value2, tok);
                    line_len = strlen(tok);
                    if ((int)value2[line_len - 1] == 10 || (int)value2[line_len - 1] == 13) {
                        if ((int)value2[line_len - 1] == 10 || (int)value2[line_len - 1] == 13)
                            remove_nl = 2;
                        else
                            remove_nl = 1;
                    } else
                        remove_nl = 0;

                    strncpy(value2, tok, line_len - remove_nl);
                    ui_print("备份文件夹设置 '%s'\n", value2);
                    if (twrp_backup_mode) {
                        char device_id[PROPERTY_VALUE_MAX];
                        get_device_id(device_id);
                        sprintf(backup_path, "%s/%s/%s/%s", other_sd, TWRP_BACKUP_PATH, device_id, value2);
                    } else {
                        sprintf(backup_path, "%s/clockworkmod/backup/%s", other_sd, value2);
                    }
                } else if (twrp_backup_mode) {
                    get_twrp_backup_path(other_sd, backup_path);
                } else {
                    get_custom_backup_path(other_sd, backup_path);
                }
                if (0 != (ret_val = ors_backup_command(backup_path, value1)))
                    ui_print("备份失败!!\n");
            } else if (strcmp(command, "restore") == 0) {
                // Restore
                tok = strtok(value, " ");
                strcpy(value1, tok);
                ui_print("正在还原 '%s'\n", value1);

                // custom restore settings
                is_custom_backup = 1;
                int old_enable_md5sum = enable_md5sum;
                enable_md5sum = 1;
                backup_boot = 0, backup_recovery = 0, backup_system = 0;
                backup_preload = 0, backup_data = 0, backup_cache = 0, backup_sdext = 0;
                ignore_android_secure = 1; //disable

                // check what type of restore we need
                if (strstr(value1, TWRP_BACKUP_PATH) != NULL)
                    twrp_backup_mode = 1;

                tok = strtok(NULL, " ");
                if (tok != NULL) {
                    memset(value2, 0, sizeof(value2));
                    strcpy(value2, tok);
                    ui_print("设置还原选项:\n");
                    line_len = strlen(value2);
                    for (i=0; i<line_len; i++) {
                        if (value2[i] == 'S' || value2[i] == 's') {
                            backup_system = 1;
                            ui_print("System\n");
                            if (nandroid_add_preload) {
                                backup_preload = 1;
                                ui_print("启用Preload分区还原.\n");
                                ui_print("启用将会延长还原时间\n");
                            }
                        } else if (value2[i] == 'D' || value2[i] == 'd') {
                            backup_data = 1;
                            ui_print("Data分区\n");
                        } else if (value2[i] == 'C' || value2[i] == 'c') {
                            backup_cache = 1;
                            ui_print("Cache分区\n");
                        } else if (value2[i] == 'R' || value2[i] == 'r') {
                            backup_recovery = 1;
                            ui_print("Recovery分区\n");
                        } else if (value2[i] == '1') {
                            ui_print("%s\n", "Option for special1 ignored in CWMR");
                        } else if (value2[i] == '2') {
                            ui_print("%s\n", "Option for special2 ignored in CWMR");
                        } else if (value2[i] == '3') {
                            ui_print("%s\n", "Option for special3 ignored in CWMR");
                        } else if (value2[i] == 'B' || value2[i] == 'b') {
                            backup_boot = 1;
                            ui_print("Boot分区\n");
                        } else if (value2[i] == 'A' || value2[i] == 'a') {
                            ignore_android_secure = 0;
                            ui_print("安全模式\n");
                        } else if (value2[i] == 'E' || value2[i] == 'e') {
                            backup_sdext = 1;
                            ui_print("SD-Ext分区\n");
                        } else if (value2[i] == 'M' || value2[i] == 'm') {
                            enable_md5sum = 0;
                            ui_print("MD5校验关闭\n");
                        }
                    }
                } else {
                    LOGI("No restore options set\n");
                    LOGI("Restoring default partitions");
                    backup_boot = 1, backup_system = 1;
                    backup_data = 1, backup_cache = 1, backup_sdext = 1;
                    ignore_android_secure = 0;
                    backup_preload = nandroid_add_preload;
                }

                if (twrp_backup_mode)
                    ret_val = twrp_restore(value1);
                else
                    ret_val = nandroid_restore(value1, backup_boot, backup_system, backup_data, backup_cache, backup_sdext, 0);
                
                if (ret_val != 0)
                    ui_print("还原失败!\n");

                is_custom_backup = 0, twrp_backup_mode = 0;
                reset_custom_job_settings(0);
                enable_md5sum = old_enable_md5sum;
            } else if (strcmp(command, "mount") == 0) {
                // Mount
                if (value[0] != '/') {
                    strcpy(mount, "/");
                    strcat(mount, value);
                } else
                    strcpy(mount, value);
                ensure_path_mounted(mount);
                ui_print("安装 '%s'\n", mount);
            } else if (strcmp(command, "unmount") == 0 || strcmp(command, "umount") == 0) {
                // Unmount
                if (value[0] != '/') {
                    strcpy(mount, "/");
                    strcat(mount, value);
                } else
                    strcpy(mount, value);
                ensure_path_unmounted(mount);
                ui_print("卸载 '%s'\n", mount);
            } else if (strcmp(command, "set") == 0) {
                // Set value
                tok = strtok(value, " ");
                strcpy(value1, tok);
                tok = strtok(NULL, " ");
                strcpy(value2, tok);
                ui_print("设置功能禁用: '%s' to '%s'\n", value1, value2);
            } else if (strcmp(command, "mkdir") == 0) {
                // Make directory (recursive)
                ui_print("禁止创建文件夹: '%s'\n", value);
            } else if (strcmp(command, "reboot") == 0) {
                // Reboot
            } else if (strcmp(command, "cmd") == 0) {
                if (cindex != 0) {
                    __system(value);
                } else {
                    LOGE("No value given for cmd\n");
                }
            } else if (strcmp(command, "print") == 0) {
                ui_print("%s\n", value);
            } else if (strcmp(command, "sideload") == 0) {
                // Install zip from sideload
                ui_print("等待电脑推送刷机包...\n");
                ensure_path_mounted("/sdcard");
                if (volume_for_path("/external_sd") != NULL)
                    ensure_path_mounted("/external_sd");
                if (volume_for_path("/emmc") != NULL)
                    ensure_path_mounted("/emmc");
                if (0 != (ret_val = apply_from_adb()))
                    LOGE("Error installing from sideload\n");
            } else {
                LOGE("Unrecognized script command: '%s'\n", command);
                ret_val = 1;
            }
        }
        fclose(fp);
        ui_print("脚本文件处理完成\n");
    } else {
        LOGE("Error opening script file '%s'\n", ors_script);
        return 1;
    }
    return ret_val;
}

//show menu: select ors from default path
static int browse_for_file = 1;
static void choose_default_ors_menu(const char* ors_path)
{
    if (ensure_path_mounted(ors_path) != 0) {
        LOGE("Can't mount %s\n", ors_path);
        browse_for_file = 1;
        return;
    }

    char ors_dir[PATH_MAX];
    sprintf(ors_dir, "%s/clockworkmod/ors/", ors_path);
    if (access(ors_dir, F_OK) == -1) {
        //custom folder does not exist
        browse_for_file = 1;
        return;
    }

    static char* headers[] = {  "选择要运行的脚本",
                                "",
                                NULL
    };

    char* ors_file = choose_file_menu(ors_dir, ".ors", headers);
    if (no_files_found == 1) {
        //0 valid files to select, let's continue browsing next locations
        ui_print("没有找到 *.ors 文件 %s/clockworkmod/ors\n", ors_path);
        browse_for_file = 1;
    } else {
        browse_for_file = 0;
        //we found ors scripts in clockworkmod/ors folder: do not proceed other locations even if no file is chosen
    }
    if (ors_file == NULL) {
        //either no valid files found or we selected no files by pressing back menu
        return;
    }
    static char* confirm_install  = "确认运行脚本?";
    static char confirm[PATH_MAX];
    sprintf(confirm, "是 - 运行 %s", basename(ors_file));
    if (confirm_selection(confirm_install, confirm)) {
        run_ors_script(ors_file);
    }
}

//show menu: browse for custom Open Recovery Script
static void choose_custom_ors_menu(const char* ors_path)
{
    if (ensure_path_mounted(ors_path) != 0) {
        LOGE("Can't mount %s\n", ors_path);
        return;
    }

    static char* headers[] = {  "选择ORS脚本运行",
                                NULL
    };

    char* ors_file = choose_file_menu(ors_path, ".ors", headers);
    if (ors_file == NULL)
        return;
    static char* confirm_install  = "确认运行脚本?";
    static char confirm[PATH_MAX];
    sprintf(confirm, "是 - 运行 %s", basename(ors_file));
    if (confirm_selection(confirm_install, confirm)) {
        run_ors_script(ors_file);
    }
}

//show menu: select sdcard volume to search for custom ors file
static void show_custom_ors_menu() {
    static char* headers[] = {  "搜索ORS脚本运行",
                                "",
                                NULL
    };

    char* list[] = { "搜索内置SD卡",
                            NULL,
                            NULL
    };

    char *other_sd = NULL;
    if (volume_for_path("/emmc") != NULL) {
        other_sd = "/emmc/";
        list[1] = "搜索内置SD卡";
    } else if (volume_for_path("/external_sd") != NULL) {
        other_sd = "/external_sd/";
        list[1] = "搜索外置SD卡";
    }

    for (;;) {
        int chosen_item = get_filtered_menu_selection(headers, list, 0, 0, sizeof(list) / sizeof(char*));
        if (chosen_item == GO_BACK)
            break;
        switch (chosen_item)
        {
            case 0:
                choose_custom_ors_menu("/sdcard/");
                break;
            case 1:
                choose_custom_ors_menu(other_sd);
                break;
        }
    }
}
//----------end open recovery script support


/**********************************/
/*       Start Get ROM Name       */
/*    Original source by PhilZ    */
/**********************************/
// formats a string to be compliant with filenames standard and limits its length to max_len
static void format_filename(char *valid_path, int max_len) {
    // remove non allowed chars (invalid file names) and limit valid_path filename to max_len chars
    // we could use a whitelist: ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_-
    char invalid_fn[] = " /><%#*^$:;\"\\\t,?!{}()=+'¦|";
    int i = 0;
    for(i=0; valid_path[i] != '\0' && i < max_len; i++) {
        int j = 0;
        while (j < strlen(invalid_fn)) {
            if (valid_path[i] == invalid_fn[j])
                valid_path[i] = '_';
            j++;
        }
        if (valid_path[i] == 13)
            valid_path[i] = '_';
    }
    valid_path[max_len] = '\0';
    if (valid_path[strlen(valid_path)-1] == '_') {
        valid_path[strlen(valid_path)-1] = '\0';
    }
}

// get rom_name function
#define MAX_ROM_NAME_LENGTH 31
void get_rom_name(char *rom_name) {
    const char *rom_id_key[] = { "ro.modversion", "ro.romversion", "ro.build.display.id", NULL };
    const char *key;
    sprintf(rom_name, "noname");
    int i = 0;
    while ((key = rom_id_key[i]) != NULL && strcmp(rom_name, "noname") == 0) {
        if (read_config_file("/system/build.prop", key, rom_name, "noname") < 0) {
            ui_print("failed to open /system/build.prop!\n");
            ui_print("using default noname.\n");
            break;
        }
        i++;
    }
    if (strcmp(rom_name, "noname") != 0) {
        format_filename(rom_name, MAX_ROM_NAME_LENGTH);
    }
}


/**********************************/
/*   Misc Nandroid Settings Menu  */
/**********************************/
void misc_nandroid_menu()
{
    static char* headers[] = {  "其他Nandroid设置",
                                "",
                                NULL
    };

    char item_md5[MENU_MAX_COLS];
    char item_preload[MENU_MAX_COLS];
    char item_compress[MENU_MAX_COLS];
    char item_ors_path[MENU_MAX_COLS];
    char item_ors_format[MENU_MAX_COLS];
    char item_size_progress[MENU_MAX_COLS];
    char item_nand_progress[MENU_MAX_COLS];
    char* list[] = { item_md5,
                    item_preload,
                    item_compress,
                    item_ors_path,
                    item_ors_format,
                    item_size_progress,
                    item_nand_progress,
                    "默认的备份格式...",
                    NULL
    };

    for (;;) {
        if (enable_md5sum) ui_format_gui_menu(item_md5, "MD5校验值", "(x)");
        else ui_format_gui_menu(item_md5, "MD5校验值", "( )");

        if (volume_for_path("/preload") == NULL)
            ui_format_gui_menu(item_preload, "包括 /preload", "N/A");
        else if (nandroid_add_preload) ui_format_gui_menu(item_preload, "包括 /preload", "(x)");
        else ui_format_gui_menu(item_preload, "包括 /preload", "( )");

        if (compression_value == TAR_GZ_LOW)
            ui_format_gui_menu(item_compress, "压缩等级", "低");
        else if (compression_value == TAR_GZ_MEDIUM)
            ui_format_gui_menu(item_compress, "压缩等级", "中");
        else if (compression_value == TAR_GZ_HIGH)
            ui_format_gui_menu(item_compress, "压缩等级", "高");
        else ui_format_gui_menu(item_compress, "压缩等级", "( )");

        char other_sd[20] = "";
        get_ors_backup_volume(other_sd);
        if (strcmp(other_sd, "") != 0)
            ui_format_gui_menu(item_ors_path,  "ORS 备份路径", other_sd);
        else ui_format_gui_menu(item_ors_path,  "ORS 备份路径", "N/A");

        if (twrp_ors_backup_format())
            ui_format_gui_menu(item_ors_format, "ORS 备份格式", "TWRP");
        else ui_format_gui_menu(item_ors_format, "ORS 备份格式", "CWM");

        if (show_nandroid_size_progress)
            ui_format_gui_menu(item_size_progress, "显示Nandroid大小进展", "(x)");
        else ui_format_gui_menu(item_size_progress, "显示Nandroid大小进展", "( )");

        int hidenandprogress = 0;
        char hidenandprogress_file[] = "/sdcard/clockworkmod/.hidenandroidprogress";
        if (ensure_path_mounted("/sdcard") == 0 && (hidenandprogress = file_found(hidenandprogress_file)) != 0)
            ui_format_gui_menu(item_nand_progress, "隐藏Nandroid进展", "(x)");
        else ui_format_gui_menu(item_nand_progress, "隐藏Nandroid进展", "( )");

        int chosen_item = get_filtered_menu_selection(headers, list, 0, 0, sizeof(list) / sizeof(char*));
        if (chosen_item == GO_BACK)
            break;
        switch (chosen_item)
        {
            case 0:
                {
                    char value[3];
                    enable_md5sum ^= 1;
                    sprintf(value, "%d", enable_md5sum);
                    write_config_file(PHILZ_SETTINGS_FILE, "nandroid_md5sum", value);
                }
                break;
            case 1:
                {
                    char value[3];
                    if (volume_for_path("/preload") == NULL)
                        nandroid_add_preload = 0;
                    else
                        nandroid_add_preload ^= 1;
                    sprintf(value, "%d", nandroid_add_preload);
                    write_config_file(PHILZ_SETTINGS_FILE, "nandroid_preload", value);
                }
                break;
            case 2:
                {
                    //switch pigz [-0, 3, 6, 9] compression level
                    char value[8];
                    compression_value += 3;
                    if (compression_value == TAR_GZ_LOW)
                        sprintf(value, "low");
                    else if (compression_value == TAR_GZ_MEDIUM)
                        sprintf(value, "medium");
                    else if (compression_value == TAR_GZ_HIGH)
                        sprintf(value, "high");
                    else {
                        compression_value = TAR_FORMAT;
                        sprintf(value, "false");
                    }
                    write_config_file(PHILZ_SETTINGS_FILE, "nandroid_compression", value);
                }
                break;
            case 3:
                {
                    if (volume_for_path("/external_sd") != NULL)
                        sprintf(other_sd, "/external_sd");
                    else if (volume_for_path("/emmc") != NULL)
                        sprintf(other_sd, "/emmc");
                    else
                        sprintf(other_sd, "");

                    if (strstr(item_ors_path, "/sdcard") != NULL)
                        write_config_file(PHILZ_SETTINGS_FILE, "ors_backup_path", other_sd);
                    else if (strstr(item_ors_path, "N/A") == NULL)
                        write_config_file(PHILZ_SETTINGS_FILE, "ors_backup_path", "/sdcard");                        
                }
                break;
            case 4:
                {
                    char value[5] = "twrp";
                    if (twrp_ors_backup_format())
                        sprintf(value, "cwm");
                    write_config_file(PHILZ_SETTINGS_FILE, "ors_backup_format", value);
                }
                break;
            case 5:
                {
                    char value[3];
                    show_nandroid_size_progress ^= 1;
                    sprintf(value, "%d", show_nandroid_size_progress);
                    write_config_file(PHILZ_SETTINGS_FILE, "show_nandroid_size_progress", value);
                }
                break;
            case 6:
                {
                    hidenandprogress ^= 1;
                    if (hidenandprogress)
                        write_string_to_file(hidenandprogress_file, "1");
                    else delete_a_file(hidenandprogress_file);
                }
                break;
            case 7:
                choose_default_backup_format();
                break;
        }
    }
}
//-------- End Misc Nandroid Settings


/****************************************/
/*  Start Install Zip from custom path  */
/*                 and                  */
/*       Free Browse Mode Support       */
/****************************************/
void set_custom_zip_path() {
    static char* headers[] = {  "设置默认根目录模式",
                                NULL
    };
    char* list_main[] = {"禁止默认根目录模式",
                            "设置内置SD卡中的文件夹",
                            NULL,
                            NULL};

    char *int_sd = "/sdcard";
    char *ext_sd = NULL;
    if (volume_for_path("/emmc") != NULL) {
        int_sd = "/emmc";
        ext_sd = "/sdcard";
    } else if (volume_for_path("/external_sd") != NULL)
        ext_sd = "/external_sd";

    if (ext_sd != NULL)
        list_main[2] = "设置外置SD卡中的文件夹";

    char custom_path[PATH_MAX];
    int chosen_item = get_menu_selection(headers, list_main, 0, 0);
    switch (chosen_item)
    {
        case 0:
            if (0 == write_config_file(PHILZ_SETTINGS_FILE, "user_zip_folder", ""))
                ui_print("禁止默认根目录模式\n");
            return;
        case 1:
            sprintf(custom_path, "%s/", int_sd);
            break;
        case 2:
            sprintf(custom_path, "%s/", ext_sd);
            break;
        default:
            return;
    }

    // populate fixed headers (display current path while browsing)
    int j = 0;
    while (headers[j]) {
        j++;
    }
    const char** fixed_headers = (const char*)malloc((j + 2) * sizeof(char*));
    j = 0;
    while (headers[j]) {
        fixed_headers[j] = headers[j];
        j++;
    }
    fixed_headers[j] = custom_path;
    fixed_headers[j + 1] = NULL;

    // start browsing for custom path
    char tmp[PATH_MAX];
    sprintf(tmp, "%s", custom_path);
    int dir_len = strlen(custom_path);
    int numDirs = 0;
    char** dirs = gather_files(custom_path, NULL, &numDirs);
    char** list = (char**) malloc((numDirs + 3) * sizeof(char*));
    list[0] = strdup("../");
    list[1] = strdup(">> 当前文件夹设置为默认 <<");
    list[numDirs+2] = NULL; // Go Back Menu

    // populate list with current folders. Reserved list[0] for ../ to browse backward
    int i;
    for(i=2; i < numDirs+2; i++) {
        list[i] = strdup(dirs[i-2] + dir_len);
    }

    for (;;) {
        chosen_item = get_menu_selection(fixed_headers, list, 0, 0);
        if (chosen_item == GO_BACK)
            break;
        if (chosen_item == 0) {
            sprintf(tmp, "%s", custom_path);
            if (strcmp(dirname(custom_path), "/") == 0)
                sprintf(custom_path, "/");
            else
                sprintf(custom_path, "%s/", dirname(tmp));
        } else if (chosen_item == 1) {
            if (strlen(custom_path) > PROPERTY_VALUE_MAX)
                LOGE("Maximum allowed path length is %d\n", PROPERTY_VALUE_MAX);
            else if (0 == write_config_file(PHILZ_SETTINGS_FILE, "user_zip_folder", custom_path)) {
                ui_print("默认安装的zip文件夹设置为 %s\n", custom_path);
                break;
            }
        } else
            sprintf(custom_path, "%s", dirs[chosen_item - 2]);

        // browse selected folder
        fixed_headers[j] = custom_path;
        dir_len = strlen(custom_path);
        numDirs = 0;
        free_string_array(list);
        free_string_array(dirs);
        dirs = gather_files(custom_path, NULL, &numDirs);
        list = (char**) malloc((numDirs + 3) * sizeof(char*));
        list[0] = strdup("../");
        list[1] = strdup(">> 当前文件夹设置为默认 <<");
        list[numDirs+2] = NULL;
        for(i=2; i < numDirs+2; i++) {
            list[i] = strdup(dirs[i-2] + dir_len);
        }
    }
    free_string_array(list);
    free_string_array(dirs);
    free(fixed_headers);
}

int show_custom_zip_menu() {
    static char* headers[] = {  "选择一个刷机包目录设为默认根目录",
                                NULL
    };

    char val[PROPERTY_VALUE_MAX];
    read_config_file(PHILZ_SETTINGS_FILE, "user_zip_folder", val, "");
    if (strcmp(val, "") == 0) {
        LOGI("默认根目录模式禁用\n");
        return 1;
    }
    if (ensure_path_mounted(val) != 0) {
        LOGE("Cannot mount custom path %s\n", val);
        LOGE("You must first setup a valid folder\n");
        LOGE("Switching to default mode\n");
        return -1;
    }

    char tmp[PATH_MAX];
    char custom_path[PATH_MAX];
    sprintf(custom_path, "%s", val);
    if (custom_path[strlen(custom_path) - 1] != '/')
        strcat(custom_path, "/");
    //LOGE("Retained val to custom_path=%s\n", custom_path);

    // populate fixed headers (display current path while browsing)
    int j = 0;
    while (headers[j]) {
        j++;
    }
    const char** fixed_headers = (const char*)malloc((j + 2) * sizeof(char*));
    j = 0;
    while (headers[j]) {
        fixed_headers[j] = headers[j];
        j++;
    }
    fixed_headers[j] = custom_path;
    fixed_headers[j + 1] = NULL;

    //gather zip files and display ../ to browse backward
    int dir_len = strlen(custom_path);
    int numDirs = 0;
    int numFiles = 0;
    int total;
    char** dirs = gather_files(custom_path, NULL, &numDirs);
    char** files = gather_files(custom_path, ".zip", &numFiles);
    total = numFiles + numDirs;
    char** list = (char**) malloc((total + 2) * sizeof(char*));
    list[0] = strdup("../");
    list[total+1] = NULL;

    // populate menu list with current folders and zip files. Reserved list[0] for ../ to browse backward
    int i;
    //LOGE(">> Dirs (num=%d):\n", numDirs);
    for(i=1; i < numDirs+1; i++) {
        list[i] = strdup(dirs[i-1] + dir_len);
        //LOGE("list[%d]=%s\n", i, list[i]);
    }
    //LOGE("\n>> Files (num=%d):\n", numFiles);
    for(i=1; i < numFiles+1; i++) {
        list[numDirs+i] = strdup(files[i-1] + dir_len);
        //LOGE("list[%d]=%s\n", numDirs+i, list[numDirs+i]);
    }

    int chosen_item;
    for (;;) {
/*
        LOGE("\n\n>> Total list:\n");
        for(i=0; i < total+1; i++) {
            LOGE("list[%d]=%s\n", i, list[i]);
        }
*/
        chosen_item = get_menu_selection(fixed_headers, list, 0, 0);
        //LOGE("\n\n>> Gathering files for chosen_item=%d:\n", chosen_item);
        if (chosen_item == GO_BACK) {
            if (strcmp(custom_path, "/") == 0)
                break;
            else chosen_item = 0;
        }
        if (chosen_item < numDirs+1 && chosen_item >= 0) {
            if (chosen_item == 0) {
                sprintf(tmp, "%s", dirname(custom_path));
                if (strcmp(tmp, "/") != 0)
                    strcat(tmp, "/");
                sprintf(custom_path, "%s", tmp);
            } else sprintf(custom_path, "%s", dirs[chosen_item - 1]);
            //LOGE("\n\n Selected chosen_item=%d is: %s\n\n", chosen_item, custom_path);

            // browse selected folder
            fixed_headers[j] = custom_path;
            dir_len = strlen(custom_path);
            numDirs = 0;
            numFiles = 0;
            free_string_array(list);
            free_string_array(files);
            free_string_array(dirs);
            dirs = gather_files(custom_path, NULL, &numDirs);
            files = gather_files(custom_path, ".zip", &numFiles);
            total = numFiles + numDirs;
            list = (char**) malloc((total + 2) * sizeof(char*));
            list[0] = strdup("../");
            list[total+1] = NULL;
                
            //LOGE(">> Dirs (num=%d):\n", numDirs);
            for(i=1; i < numDirs+1; i++) {
                list[i] = strdup(dirs[i-1] + dir_len);
                //LOGE("list[%d]=%s\n", i, list[i]);
            }
            //LOGE("\n>> Files (num=%d):\n", numFiles);
            for(i=1; i < numFiles+1; i++) {
                list[numDirs+i] = strdup(files[i-1] + dir_len);
                //LOGE("list[%d]=%s\n", numDirs+i, list[numDirs+i]);
            }
        } else if (chosen_item > numDirs && chosen_item < total+1) {
            // we selected a zip file to install
            break;
        }
    }
/*
    LOGE("\n\n>> Selected dir contains:\n");
    for(i=0; i < total+1; i++) {
        LOGE("list[%d]=%s\n", i, list[i]);
    }
*/
    //flashing selected zip file
    if (chosen_item !=  GO_BACK) {
        sprintf(tmp, "Yes - Install %s", list[chosen_item]);
        if (confirm_selection("Install selected file?", tmp))
            install_zip(files[chosen_item - numDirs - 1]);
    }
    free_string_array(list);
    free_string_array(files);
    free_string_array(dirs);
    free(fixed_headers);
    return 0;
}
//-------- End Free Browse Mode


/*****************************************/
/*   Custom Backup and Restore Support   */
/*       code written by PhilZ @xda      */
/*        for PhilZ Touch Recovery       */
/*****************************************/
static void choose_delete_folder(const char* path) {
    if (ensure_path_mounted(path) != 0) {
        LOGE("Can't mount %s\n", path);
        return;
    }

    static char* headers[] = {  "选择要删除的文件夹",
                                NULL
    };

    char* file = choose_file_menu(path, NULL, headers);
    if (file == NULL)
        return;

    char tmp[PATH_MAX];
    sprintf(tmp, "是 - 删除 %s", basename(file));
    if (confirm_selection("确认删除?", tmp)) {
        sprintf(tmp, "rm -rf '%s'", file);
        __system(tmp);
    }
}

// actually only used to delete twrp backups
static void delete_custom_backups(const char* backup_path)
{
    static char* headers[] = {"查看备份文件夹...", NULL};

    char* list[] = {"从内置SD卡中删除",
                    NULL,
                    NULL};

    char *int_sd = "/sdcard";
    char *ext_sd = NULL;
    if (volume_for_path("/emmc") != NULL) {
        int_sd = "/emmc";
        ext_sd = "/sdcard";
    } else if (volume_for_path("/external_sd") != NULL)
        ext_sd = "/external_sd";

    if (ext_sd != NULL)
        list[1] = "从外置SD卡中删除";

    int chosen_item = get_menu_selection(headers, list, 0, 0);
    switch (chosen_item)
    {
        case 0:
            {
                char tmp[PATH_MAX];
                sprintf(tmp, "%s/%s/", int_sd, backup_path);
                choose_delete_folder(tmp);
            }
            break;
        case 1:
            {
                char tmp[PATH_MAX];
                sprintf(tmp, "%s/%s/", ext_sd, backup_path);
                choose_delete_folder(tmp);
            }
            break;
    }
}

/*
- get_android_secure_path() should be called each time we want to backup/restore .android_secure
- it will always favor external storage
- it will format path to retained android_secure location and set android_secure_ext to 1 or 0
- android_secure_ext = 1, will allow nandroid processing of android_secure partition
- to force other storage, user must keep only one .android_secure folder in one of the sdcards
- for /data/media devices, only second storage is allowed, not /sdcard
- custom backup and restore jobs (incl twrp and ors modes) can force .android_secure to be ignored
  this is done by setting ignore_android_secure to 1
- ignore_android_secure is by default 0 ad will be reset to 0 by reset_custom_job_settings()
*/
int get_android_secure_path(char *and_sec_path) {
    if (ignore_android_secure)
        return android_secure_ext = 0;

    android_secure_ext = 1;
    struct stat st;
    if (volume_for_path("/external_sd") != NULL &&
                ensure_path_mounted("/external_sd") == 0 &&
                stat("/external_sd/.android_secure", &st) == 0) {
        strcpy(and_sec_path, "/external_sd/.android_secure");
    }
    else if (!is_data_media() && ensure_path_mounted("/sdcard") == 0 && 
                stat("/sdcard/.android_secure", &st) == 0) {
        strcpy(and_sec_path, "/sdcard/.android_secure");
    }
    else if (volume_for_path("/emmc") != NULL &&
                ensure_path_mounted("/emmc") == 0 &&
                stat("/emmc/.android_secure", &st) == 0) {
        strcpy(and_sec_path, "/emmc/.android_secure");
    }
    else android_secure_ext = 0;
    
    return android_secure_ext;
}

void reset_custom_job_settings(int custom_job) {
    if (custom_job) {
        backup_boot = 1, backup_recovery = 1, backup_system = 1;
        backup_data = 1, backup_cache = 1;
        backup_wimax = 0;
        backup_sdext = 0;
        if (twrp_backup_mode)
            backup_wimax = 0;
    } else {
        backup_boot = 1, backup_recovery = 1, backup_system = 1;
        backup_data = 1, backup_cache = 1;
        backup_wimax = 1;
        backup_sdext = 1;
    }

    backup_preload = 0;
    backup_modem = 0;
    backup_radio = 0;
    backup_efs = 0;
    backup_misc = 0;
    ignore_android_secure = 0;
    reboot_after_nandroid = 0;
}

static void ui_print_backup_list() {
    ui_print("This will process");
    if (backup_boot)
        ui_print(" - boot");
    if (backup_recovery)
        ui_print(" - recovery");
    if (backup_system)
        ui_print(" - system");
    if (backup_preload)
        ui_print(" - preload");
    if (backup_data)
        ui_print(" - data");
    if (backup_cache)
        ui_print(" - cache");
    if (backup_sdext)
        ui_print(" - sd-ext");
    if (backup_modem)
        ui_print(" - modem");
    if (backup_radio)
        ui_print(" - radio");
    if (backup_wimax)
        ui_print(" - wimax");
    if (backup_efs)
        ui_print(" - efs");
    if (backup_misc)
        ui_print(" - misc");
    ui_print("!\n");
}

void get_custom_backup_path(const char* sd_path, char *backup_path) {
    char rom_name[PROPERTY_VALUE_MAX] = "noname";
    get_rom_name(rom_name);

    time_t t = time(NULL);
    struct tm *timeptr = localtime(&t);
    if (timeptr == NULL) {
        struct timeval tp;
        gettimeofday(&tp, NULL);
        if (backup_efs)
            sprintf(backup_path, "%s/%s/%d", sd_path, EFS_BACKUP_PATH, tp.tv_sec);
        else
            sprintf(backup_path, "%s/%s/%d_%s", sd_path, "clockworkmod/backup", tp.tv_sec, rom_name);
    } else {
        char tmp[PATH_MAX];
        strftime(tmp, sizeof(tmp), "%F.%H.%M.%S", timeptr);
        if (backup_efs)
            sprintf(backup_path, "%s/%s/%s", sd_path, EFS_BACKUP_PATH, tmp);
        else
            sprintf(backup_path, "%s/%s/%s_%s", sd_path, "clockworkmod/backup", tmp, rom_name);
    }
}

static void custom_backup_handler() {
    static char* headers[] = {"选择自定义备份目录", "", NULL};
    char* list[] = {"备份到内置SD卡",
                        NULL,
                        NULL};

    ui_print_backup_list();

    char *int_sd = "/sdcard";
    char *ext_sd = NULL;
    if (volume_for_path("/emmc") != NULL) {
        int_sd = "/emmc";
        ext_sd = "/sdcard";
    } else if (volume_for_path("/external_sd") != NULL)
        ext_sd = "/external_sd";

    if (ext_sd != NULL)
        list[1] = "备份到外置SD卡";

    int chosen_item = get_menu_selection(headers, list, 0, 0);
    switch (chosen_item)
    {
        case 0:
            {
                if (ensure_path_mounted(int_sd) == 0) {
                    char backup_path[PATH_MAX] = "";
                    get_custom_backup_path(int_sd, backup_path);
                    nandroid_backup(backup_path);
                } else {
                    ui_print("无法挂载 %s\n", int_sd);
                }
            }
            break;
        case 1:
            {
                if (ensure_path_mounted(ext_sd) == 0) {
                    char backup_path[PATH_MAX] = "";
                    get_custom_backup_path(ext_sd, backup_path);
                    nandroid_backup(backup_path);
                } else {
                    ui_print("无法挂载 %s\n", ext_sd);
                }
            }
            break;
    }
}

static void custom_restore_handler(const char* backup_path) {
    if (ensure_path_mounted(backup_path) != 0) {
        LOGE("Can't mount %s\n", backup_path);
        return;
    }

    static char* headers[] = {  "选择要还原的备份",
                                NULL
    };

    struct statfs s;
    char* file = NULL;
    static char* confirm_install = "从这个备份还原?";
    char tmp[PATH_MAX];
    char *backup_source;

    if (backup_efs == RESTORE_EFS_IMG) {
        if (volume_for_path("/efs") == NULL) {
            LOGE("No /efs partition to flash\n");
            return;
        }
        file = choose_file_menu(backup_path, ".img", headers);
        if (file == NULL) {
            //either no valid files found or we selected no files by pressing back menu
            if (no_files_found)
                ui_print("无法还原 %s !\n", backup_path);
            return;
        }

        //restore efs raw image
        backup_source = basename(file);
        ui_print("%s 还原到 /efs!\n", backup_source);
        sprintf(tmp, "是 - 还原 %s", backup_source);
        if (confirm_selection(confirm_install, tmp))
            dd_raw_restore_handler(file, "/efs");
    } else if (backup_efs == RESTORE_EFS_TAR) {
        if (volume_for_path("/efs") == NULL) {
            LOGE("No /efs partition to flash\n");
            return;
        }
        file = choose_file_menu(backup_path, NULL, headers);
        if (file == NULL) {
            if (no_files_found)
                ui_print("无法还原 %s !\n", backup_path);
            return;
        }

        sprintf(tmp, "%s/efs.img", file);
        if (0 == statfs(tmp, &s)) {
            ui_print("检测到efs.img文件在 %s!\n", file);
            ui_print("选择efs.img文件还原或删除,\n");
            return;
        }

        //restore efs from nandroid tar format
        ui_print("%s 将还原到 /efs!\n", file);
        sprintf(tmp, "是 - 还原 %s", basename(file));
        if (confirm_selection(confirm_install, tmp))
            nandroid_restore(file, 0, 0, 0, 0, 0, 0);
    } else if (backup_modem == RAW_BIN_FILE) {
        file = choose_file_menu(backup_path, ".bin", headers);
        if (file == NULL) {
            //either no valid files found or we selected no files by pressing back menu
            if (no_files_found)
                ui_print("无法还原 %s !\n", backup_path);
            return;
        }

        //restore modem.bin raw image
        backup_source = basename(file);
        Volume *vol = volume_for_path("/modem");
        if (vol != NULL) {
            ui_print("%s 还原到 /modem!\n", backup_source);
            char confirm[PATH_MAX];
            sprintf(confirm, "是 - 还原 %s", backup_source);
            if (confirm_selection(confirm_install, confirm))
                dd_raw_restore_handler(file, "/modem");
        } else
            LOGE("无法还原 /modem\n");
    } else if (backup_radio == RAW_BIN_FILE) {
        file = choose_file_menu(backup_path, ".bin", headers);
        if (file == NULL) {
            if (no_files_found)
                ui_print("无法还原 %s !\n", backup_path);
            return;
        }

        //restore radio.bin raw image
        backup_source = basename(file);
        Volume *vol = volume_for_path("/radio");
        if (vol != NULL) {
            ui_print("%s 还原到 /radio!\n", backup_source);
            char confirm[PATH_MAX];
            sprintf(confirm, "是 - 还原 %s", backup_source);
            if (confirm_selection(confirm_install, confirm))
                dd_raw_restore_handler(file, "/radio");
        } else
            LOGE("无法还原 /radio\n");
    } else {
        //process restore job
        file = choose_file_menu(backup_path, "", headers);
        if (file == NULL) {
            if (no_files_found)
                ui_print("无法还原 %s !\n", backup_path);
            return;
        }
        backup_source = dirname(file);
        ui_print("%s 将还原到指定的分区!\n", backup_source);
        sprintf(tmp, "是 - 还原 %s", basename(backup_source));
        if (confirm_selection(confirm_install, tmp)) {
            nandroid_restore(backup_source, backup_boot, backup_system, backup_data, backup_cache, backup_sdext, backup_wimax);
        }
    }
}

static void browse_backup_folders(const char* backup_path)
{
    static char* headers[] = {"查看备份文件夹...", "", NULL};

    char* list[] = {"从内置SD卡还原",
                    NULL,
                    NULL};

    ui_print_backup_list();

    char *int_sd = "/sdcard";
    char *ext_sd = NULL;
    if (volume_for_path("/emmc") != NULL) {
        int_sd = "/emmc";
        ext_sd = "/sdcard";
    } else if (volume_for_path("/external_sd") != NULL)
        ext_sd = "/external_sd";

    if (ext_sd != NULL)
        list[1] = "从外置SD卡还原";

    int chosen_item = get_menu_selection(headers, list, 0, 0);
    switch (chosen_item)
    {
        case 0:
            {
                char tmp[PATH_MAX];
                sprintf(tmp, "%s/%s/", int_sd, backup_path);
                if (twrp_backup_mode)
                    twrp_restore_handler(tmp);
                else
                    custom_restore_handler(tmp);
            }
            break;
        case 1:
            {
                char tmp[PATH_MAX];
                sprintf(tmp, "%s/%s/", ext_sd, backup_path);
                if (twrp_backup_mode)
                    twrp_restore_handler(tmp);
                else
                    custom_restore_handler(tmp);
            }
            break;
    }
}

/*
* custom backup and restore jobs:
    - At least one partition to restore must be selected
* restore jobs
    - modem.bin and radio.bin file types must be restored alone (available only in custom restore mode)
    - TWRP restore:
        + accepts efs to be restored along other partitions (but modem is never of bin type and preload is always 0)
    - Custom jobs:
        + efs must be restored alone (except for twrp backup jobs)
        + else, all other tasks can be processed
* backup jobs
    - if it is a twrp backup job, we can accept efs with other partitions
    - else, we only accept them separately for custom backup jobs    
*/
static void validate_backup_job(const char* backup_path) {
    int sum = backup_boot + backup_recovery + backup_system + backup_preload + backup_data +
                backup_cache + backup_sdext + backup_wimax + backup_misc;
    if (0 == (sum + backup_efs + backup_modem + backup_radio)) {
        ui_print("至少选择一个要还原的分区!\n");
        return;
    }

    if (backup_path != NULL)
    {
        // it is a restore job
        if (backup_modem == RAW_BIN_FILE) {
            if (0 != (sum + backup_efs + backup_radio))
                ui_print("modem.bin 格式必须单独还原!\n");
            else
                browse_backup_folders(MODEM_BIN_PATH);
        }
        else if (backup_radio == RAW_BIN_FILE) {
            if (0 != (sum + backup_efs + backup_modem))
                ui_print("radio.bin 格式必须单独还原!\n");
            else
                browse_backup_folders(RADIO_BIN_PATH);
        }
        else if (twrp_backup_mode)
            browse_backup_folders(backup_path);
        else if (backup_efs && (sum + backup_modem + backup_radio) != 0)
            ui_print("efs 必须单独还原!\n");
        else if (backup_efs && (sum + backup_modem + backup_radio) == 0)
            browse_backup_folders(EFS_BACKUP_PATH);
        else
            browse_backup_folders(backup_path);
    }
    else
    {
        // it is a backup job to validate
        if (nandroid_get_default_backup_format() != NANDROID_BACKUP_FORMAT_TAR)
            LOGE("默认备份格式必须 tar!\n");
        else if (twrp_backup_mode)
            twrp_backup_handler();
        else if (backup_efs && (sum + backup_modem + backup_radio) != 0)
            ui_print("efs 必须单独进行备份!\n");
        else
            custom_backup_handler();
    }
}

// we'd better do some malloc here... later
static void custom_restore_menu(const char* backup_path) {
    static char* headers[] = {  "自定义还原设置",
                                NULL
    };

    char item_boot[MENU_MAX_COLS];
    char item_recovery[MENU_MAX_COLS];
    char item_system[MENU_MAX_COLS];
    char item_preload[MENU_MAX_COLS];
    char item_data[MENU_MAX_COLS];
    char item_andsec[MENU_MAX_COLS];
    char item_cache[MENU_MAX_COLS];
    char item_sdext[MENU_MAX_COLS];
    char item_modem[MENU_MAX_COLS];
    char item_radio[MENU_MAX_COLS];
    char item_efs[MENU_MAX_COLS];
    char item_misc[MENU_MAX_COLS];
    char item_reboot[MENU_MAX_COLS];
    char item_wimax[MENU_MAX_COLS];
    char* list[] = { item_boot,
                item_recovery,
                item_system,
                item_preload,
                item_data,
                item_andsec,
                item_cache,
                item_sdext,
                item_modem,
                item_radio,
                item_efs,
                item_misc,
                ">> 启动自定义还原设置 <<",
                item_reboot,
                NULL,
                NULL
    };

    char tmp[PATH_MAX];
    if (0 == get_partition_device("wimax", tmp)) {
        // show wimax restore option
        list[14] = "show wimax menu";
    }

    reset_custom_job_settings(1);
    for (;;) {
        if (backup_boot) ui_format_gui_menu(item_boot, "还原 boot", "(x)");
        else ui_format_gui_menu(item_boot, "还原 boot", "( )");

        if (backup_recovery) ui_format_gui_menu(item_recovery, "还原 recovery", "(x)");
        else ui_format_gui_menu(item_recovery, "还原 recovery", "( )");

        if (backup_system) ui_format_gui_menu(item_system, "还原 system", "(x)");
        else ui_format_gui_menu(item_system, "还原 system", "( )");

        if (volume_for_path("/preload") == NULL)
            ui_format_gui_menu(item_preload, "还原 preload", "N/A");
        else if (backup_preload) ui_format_gui_menu(item_preload, "还原 preload", "(x)");
        else ui_format_gui_menu(item_preload, "还原 preload", "( )");

        if (backup_data) ui_format_gui_menu(item_data, "还原 data", "(x)");
        else ui_format_gui_menu(item_data, "还原 data", "( )");

        get_android_secure_path(tmp);
        if (backup_data && android_secure_ext)
            ui_format_gui_menu(item_andsec, "还原 and-sec", dirname(tmp));
        else ui_format_gui_menu(item_andsec, "还原 and-sec", "( )");

        if (backup_cache) ui_format_gui_menu(item_cache, "还原 cache", "(x)");
        else ui_format_gui_menu(item_cache, "还原 cache", "( )");

        if (backup_sdext) ui_format_gui_menu(item_sdext, "还原 sd-ext", "(x)");
        else ui_format_gui_menu(item_sdext, "还原 sd-ext", "( )");

        if (volume_for_path("/modem") == NULL)
            ui_format_gui_menu(item_modem, "还原 modem", "N/A");
        else if (backup_modem == RAW_IMG_FILE)
            ui_format_gui_menu(item_modem, "还原 modem [.img]", "(x)");
        else if (backup_modem == RAW_BIN_FILE)
            ui_format_gui_menu(item_modem, "还原 modem [.bin]", "(x)");
        else ui_format_gui_menu(item_modem, "还原 modem", "( )");

        if (volume_for_path("/radio") == NULL)
            ui_format_gui_menu(item_radio, "还原 radio", "N/A");
        else if (backup_radio == RAW_IMG_FILE)
            ui_format_gui_menu(item_radio, "还原 radio [.img]", "(x)");
        else if (backup_radio == RAW_BIN_FILE)
            ui_format_gui_menu(item_radio, "还原 radio [.bin]", "(x)");
        else ui_format_gui_menu(item_radio, "还原 radio", "( )");

        if (volume_for_path("/efs") == NULL)
            ui_format_gui_menu(item_efs, "还原 efs", "N/A");
        else if (backup_efs == RESTORE_EFS_IMG)
            ui_format_gui_menu(item_efs, "还原 efs [.img]", "(x)");
        else if (backup_efs == RESTORE_EFS_TAR)
            ui_format_gui_menu(item_efs, "还原 efs [.tar]", "(x)");
        else ui_format_gui_menu(item_efs, "还原 efs", "( )");

        if (volume_for_path("/misc") == NULL)
            ui_format_gui_menu(item_misc, "还原 misc", "N/A");
        else if (backup_misc) ui_format_gui_menu(item_misc, "还原 misc", "(x)");
        else ui_format_gui_menu(item_misc, "还原 misc", "( )");

        if (reboot_after_nandroid) ui_format_gui_menu(item_reboot, "重新启动生效", "(x)");
        else ui_format_gui_menu(item_reboot, "重新启动生效", "( )");

        if (NULL != list[14]) {
            if (backup_wimax)
                ui_format_gui_menu(item_wimax, "还原 WiMax", "(x)");
            else ui_format_gui_menu(item_wimax, "还原 WiMax", "( )");
            list[14] = item_wimax;
        }


        int chosen_item = get_filtered_menu_selection(headers, list, 0, 0, sizeof(list) / sizeof(char*));
        if (chosen_item == GO_BACK)
            break;
        switch (chosen_item)
        {
            case 0:
                backup_boot ^= 1;
                break;
            case 1:
                backup_recovery ^= 1;
                break;
            case 2:
                backup_system ^= 1;
                break;
            case 3:
                if (volume_for_path("/preload") == NULL)
                    backup_preload = 0;
                else backup_preload ^= 1;
                break;
            case 4:
                backup_data ^= 1;
                break;
            case 5:
                ignore_android_secure ^= 1;
                if (!ignore_android_secure && has_second_storage())
                    ui_print("要强制还原到第二个存储，只保留一个android_secure文件夹\n");
                break;
            case 6:
                backup_cache ^= 1;
                break;
            case 7:
                backup_sdext ^= 1;
                break;
            case 8:
                if (volume_for_path("/modem") == NULL)
                    backup_modem = 0;
                else {
                    backup_modem++;
                    if (backup_modem > 2)
                        backup_modem = 0;
                    if (twrp_backup_mode && backup_modem == RAW_BIN_FILE)
                        backup_modem = 0;
                }
                break;
            case 9:
                if (volume_for_path("/radio") == NULL)
                    backup_radio = 0;
                else {
                    backup_radio++;
                    if (backup_radio > 2)
                        backup_radio = 0;
                    if (twrp_backup_mode && backup_radio == RAW_BIN_FILE)
                        backup_radio = 0;
                }
                break;
            case 10:
                if (volume_for_path("/efs") == NULL)
                    backup_efs = 0;
                else {
                    backup_efs++;
                    if (backup_efs > 2)
                        backup_efs = 0;
                    if (twrp_backup_mode && backup_efs == RESTORE_EFS_IMG)
                        backup_efs = 0;
                }
                break;
            case 11:
                if (volume_for_path("/misc") == NULL)
                    backup_misc = 0;
                else backup_misc ^= 1;
                break;
            case 12:
                validate_backup_job(backup_path);
                break;
            case 13:
                reboot_after_nandroid ^= 1;
                break;
            case 14:
                if (twrp_backup_mode) backup_wimax = 0;
                else backup_wimax ^= 1;
                break;
        }
    }
    reset_custom_job_settings(0);
}

static void custom_backup_menu() {
    static char* headers[] = {  "自定义备份设置",
                                NULL
    };

    char item_boot[MENU_MAX_COLS];
    char item_recovery[MENU_MAX_COLS];
    char item_system[MENU_MAX_COLS];
    char item_preload[MENU_MAX_COLS];
    char item_data[MENU_MAX_COLS];
    char item_andsec[MENU_MAX_COLS];
    char item_cache[MENU_MAX_COLS];
    char item_sdext[MENU_MAX_COLS];
    char item_modem[MENU_MAX_COLS];
    char item_radio[MENU_MAX_COLS];
    char item_efs[MENU_MAX_COLS];
    char item_misc[MENU_MAX_COLS];
    char item_reboot[MENU_MAX_COLS];
    char item_wimax[MENU_MAX_COLS];
    char* list[] = { item_boot,
                item_recovery,
                item_system,
                item_preload,
                item_data,
                item_andsec,
                item_cache,
                item_sdext,
                item_modem,
                item_radio,
                item_efs,
                item_misc,
                ">> 启动自定义备份设置 <<",
                item_reboot,
                NULL,
                NULL
    };

    char tmp[PATH_MAX];
    if (volume_for_path("/wimax") != NULL) {
        // show wimax backup option
        list[14] = "show wimax menu";
    }

    reset_custom_job_settings(1);
    for (;;) {
        if (backup_boot) ui_format_gui_menu(item_boot, "备份 boot", "(x)");
        else ui_format_gui_menu(item_boot, "备份 boot", "( )");

        if (backup_recovery) ui_format_gui_menu(item_recovery, "备份 recovery", "(x)");
        else ui_format_gui_menu(item_recovery, "备份 recovery", "( )");

        if (backup_system) ui_format_gui_menu(item_system, "备份 system", "(x)");
        else ui_format_gui_menu(item_system, "备份 system", "( )");

        if (volume_for_path("/preload") == NULL)
            ui_format_gui_menu(item_preload, "备份 preload", "N/A");
        else if (backup_preload) ui_format_gui_menu(item_preload, "备份 preload", "(x)");
        else ui_format_gui_menu(item_preload, "备份 preload", "( )");

        if (backup_data) ui_format_gui_menu(item_data, "备份 data", "(x)");
        else ui_format_gui_menu(item_data, "备份 data", "( )");

        get_android_secure_path(tmp);
        if (backup_data && android_secure_ext)
            ui_format_gui_menu(item_andsec, "备份 and-sec", dirname(tmp));
        else ui_format_gui_menu(item_andsec, "备份 and-sec", "( )");

        if (backup_cache) ui_format_gui_menu(item_cache, "备份 cache", "(x)");
        else ui_format_gui_menu(item_cache, "备份 cache", "( )");

        if (backup_sdext) ui_format_gui_menu(item_sdext, "备份 sd-ext", "(x)");
        else ui_format_gui_menu(item_sdext, "备份 sd-ext", "( )");

        if (volume_for_path("/modem") == NULL)
            ui_format_gui_menu(item_modem, "备份 modem", "N/A");
        else if (backup_modem) ui_format_gui_menu(item_modem, "备份 modem [.img]", "(x)");
        else ui_format_gui_menu(item_modem, "备份 modem", "( )");

        if (volume_for_path("/radio") == NULL)
            ui_format_gui_menu(item_radio, "Backup radio", "N/A");
        else if (backup_radio) ui_format_gui_menu(item_radio, "备份 radio [.img]", "(x)");
        else ui_format_gui_menu(item_radio, "备份 radio", "( )");

        if (volume_for_path("/efs") == NULL)
            ui_format_gui_menu(item_efs, "备份 efs", "N/A");
        else if (backup_efs && twrp_backup_mode)
            ui_format_gui_menu(item_efs, "备份 efs", "(x)");
        else if (backup_efs && !twrp_backup_mode)
            ui_format_gui_menu(item_efs, "备份 efs [img&tar]", "(x)");
        else ui_format_gui_menu(item_efs, "备份 efs", "( )");

        if (volume_for_path("/misc") == NULL)
            ui_format_gui_menu(item_misc, "备份 misc", "N/A");
        else if (backup_misc) ui_format_gui_menu(item_misc, "备份 misc", "(x)");
        else ui_format_gui_menu(item_misc, "备份 misc", "( )");

        if (reboot_after_nandroid) ui_format_gui_menu(item_reboot, "重新启动生效", "(x)");
        else ui_format_gui_menu(item_reboot, "重新启动生效", "( )");

        if (NULL != list[14]) {
            if (backup_wimax)
                ui_format_gui_menu(item_wimax, "备份 WiMax", "(x)");
            else ui_format_gui_menu(item_wimax, "备份 WiMax", "( )");
            list[14] = item_wimax;
        }

        int chosen_item = get_filtered_menu_selection(headers, list, 0, 0, sizeof(list) / sizeof(char*));
        if (chosen_item == GO_BACK)
            break;
        switch (chosen_item)
        {
            case 0:
                backup_boot ^= 1;
                break;
            case 1:
                backup_recovery ^= 1;
                break;
            case 2:
                backup_system ^= 1;
                break;
            case 3:
                if (volume_for_path("/preload") == NULL)
                    backup_preload = 0;
                else backup_preload ^= 1;
                break;
            case 4:
                backup_data ^= 1;
                break;
            case 5:
                ignore_android_secure ^= 1;
                if (!ignore_android_secure && has_second_storage())
                    ui_print("要强制从第二个存储备份，只保留一个android_secure文件夹\n");
                break;
            case 6:
                backup_cache ^= 1;
                break;
            case 7:
                backup_sdext ^= 1;
                break;
            case 8:
                if (volume_for_path("/modem") == NULL)
                    backup_modem = 0;
                else backup_modem ^= 1;
                break;
            case 9:
                if (volume_for_path("/radio") == NULL)
                    backup_radio = 0;
                else backup_radio ^= 1;
                break;
            case 10:
                if (volume_for_path("/efs") == NULL)
                    backup_efs = 0;
                else backup_efs ^= 1;
                break;
            case 11:
                if (volume_for_path("/misc") == NULL)
                    backup_misc = 0;
                else backup_misc ^= 1;
                break;
            case 12:
                validate_backup_job(NULL);
                break;
            case 13:
                reboot_after_nandroid ^= 1;
                break;
            case 14:
                if (twrp_backup_mode) backup_wimax = 0;
                else backup_wimax ^= 1;
                break;
        }
    }
    reset_custom_job_settings(0);
}
//------- end Custom Backup and Restore functions


/*****************************************/
/* Part of TWRP Backup & Restore Support */
/*    Original CWM port by PhilZ @xda    */
/*    Original TWRP code by Dees_Troy    */
/*         (dees_troy at yahoo)          */
/*****************************************/
int check_twrp_md5sum(const char* backup_path) {
    char tmp[PATH_MAX];
    int numFiles = 0;
    ensure_path_mounted(backup_path);
    strcpy(tmp, backup_path);
    if (strcmp(tmp + strlen(tmp) - 1, "/") != 0)
        strcat(tmp, "/");

    ui_print("\n>> 正在校验MD5值...\n");
    char** files = gather_files(tmp, ".md5", &numFiles);
    if (numFiles == 0) {
        ui_print("发现没有MD5校验和文件 %s\n", tmp);
        free_string_array(files);
        return -1;
    }

    int i = 0;
    for(i=0; i < numFiles; i++) {
        sprintf(tmp, "cd '%s' && md5sum -c '%s'", backup_path, basename(files[i]));
        if (0 != __system(tmp)) {
            ui_print("MD5校验值错误 %s!\n", basename(files[i]));
            free_string_array(files);
            return -1;
        }
    }

    ui_print("校验MD5值完成.\n");
    free_string_array(files);
    return 0;
}

int gen_twrp_md5sum(const char* backup_path) {
    ui_print("\n>> 正在生成MD5校验值...\n");
    ensure_path_mounted(backup_path);
    char tmp[PATH_MAX];
    int numFiles = 0;
    sprintf(tmp, "%s/", backup_path);
    // this will exclude subfolders!
    char** files = gather_files(tmp, "", &numFiles);
    if (numFiles == 0) {
        ui_print("找不到文件在备份路径 %s\n", tmp);
        free_string_array(files);
        return -1;
    }

    int i = 0;
    for(i=0; i < numFiles; i++) {
        sprintf(tmp, "cd '%s'; md5sum '%s' > '%s.md5'", backup_path, basename(files[i]), basename(files[i]));
        if (0 != __system(tmp)) {
            ui_print("生成MD5校验值错误 %s!\n", files[i]);
            free_string_array(files);
            return -1;
        }
    }

    ui_print("创建MD5校验值.\n");
    free_string_array(files);
    return 0;
}

// Device ID functions
static void sanitize_device_id(char *device_id) {
    const char* whitelist ="abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890-._";
    char str[PROPERTY_VALUE_MAX];
    char* c = str;

    strcpy(str, device_id);
    char tmp[PROPERTY_VALUE_MAX];
    memset(tmp, 0, sizeof(tmp));
    while (*c) {
        if (strchr(whitelist, *c))
            strncat(tmp, c, 1);
        c++;
    }
    strcpy(device_id, tmp);
    return;
}

#define CMDLINE_SERIALNO        "androidboot.serialno="
#define CMDLINE_SERIALNO_LEN    (strlen(CMDLINE_SERIALNO))
#define CPUINFO_SERIALNO        "Serial"
#define CPUINFO_SERIALNO_LEN    (strlen(CPUINFO_SERIALNO))
#define CPUINFO_HARDWARE        "Hardware"
#define CPUINFO_HARDWARE_LEN    (strlen(CPUINFO_HARDWARE))

void get_device_id(char *device_id) {
    // First try system properties
    property_get("ro.serialno", device_id, "");
    if (strlen(device_id) != 0) {
        sanitize_device_id(device_id);
        LOGI("Using ro.serialno='%s'\n", device_id);
        return;
    }
    property_get("ro.boot.serialno", device_id, "");
    if (strlen(device_id) != 0) {
        sanitize_device_id(device_id);
        LOGI("Using ro.boot.serialno='%s'\n", device_id);
        return;
    }

    // device_id not found, looking elsewhere
    FILE *fp;
    char line[2048];
    char hardware_id[32];
    char* token;

    // Assign a blank device_id to start with
    device_id[0] = 0;

    // Try the cmdline to see if the serial number was supplied
    fp = fopen("/proc/cmdline", "rt");
    if (fp != NULL)
    {
        // First step, read the line. For cmdline, it's one long line
        LOGI("Checking cmdline for serialno...\n");
        fgets(line, sizeof(line), fp);
        fclose(fp);

        // Now, let's tokenize the string
        token = strtok(line, " ");
        if (strlen(token) > PROPERTY_VALUE_MAX)
            token[PROPERTY_VALUE_MAX] = 0;

        // Let's walk through the line, looking for the CMDLINE_SERIALNO token
        while (token)
        {
            // We don't need to verify the length of token, because if it's too short, it will mismatch CMDLINE_SERIALNO at the NULL
            if (memcmp(token, CMDLINE_SERIALNO, CMDLINE_SERIALNO_LEN) == 0)
            {
                // We found the serial number!
                strcpy(device_id, token + CMDLINE_SERIALNO_LEN);
                sanitize_device_id(device_id);
                LOGI("Using serialno='%s'\n", device_id);
                return;
            }
            token = strtok(NULL, " ");
        }
    }

    // Now we'll try cpuinfo for a serial number (we shouldn't reach here as it gives wired output)
    fp = fopen("/proc/cpuinfo", "rt");
    if (fp != NULL)
    {
        LOGI("Checking cpuinfo...\n");
        while (fgets(line, sizeof(line), fp) != NULL) { // First step, read the line.
            if (memcmp(line, CPUINFO_SERIALNO, CPUINFO_SERIALNO_LEN) == 0)  // check the beginning of the line for "Serial"
            {
                // We found the serial number!
                token = line + CPUINFO_SERIALNO_LEN; // skip past "Serial"
                while ((*token > 0 && *token <= 32 ) || *token == ':') token++; // skip over all spaces and the colon
                if (*token != 0) {
                    token[30] = 0;
                    if (token[strlen(token)-1] == 10) { // checking for endline chars and dropping them from the end of the string if needed
                        char tmp[PROPERTY_VALUE_MAX];
                        memset(tmp, 0, sizeof(tmp));
                        strncpy(tmp, token, strlen(token) - 1);
                        strcpy(device_id, tmp);
                    } else {
                        strcpy(device_id, token);
                    }
                    fclose(fp);
                    sanitize_device_id(device_id);
                    LOGI("=> Using cpuinfo serialno: '%s'\n", device_id);
                    return;
                }
            } else if (memcmp(line, CPUINFO_HARDWARE, CPUINFO_HARDWARE_LEN) == 0) {
                // We're also going to look for the hardware line in cpuinfo and save it for later in case we don't find the device ID
                // We found the hardware ID
                token = line + CPUINFO_HARDWARE_LEN; // skip past "Hardware"
                while ((*token > 0 && *token <= 32 ) || *token == ':')  token++; // skip over all spaces and the colon
                if (*token != 0) {
                    token[30] = 0;
                    if (token[strlen(token)-1] == 10) { // checking for endline chars and dropping them from the end of the string if needed
                        memset(hardware_id, 0, sizeof(hardware_id));
                        strncpy(hardware_id, token, strlen(token) - 1);
                    } else {
                        strcpy(hardware_id, token);
                    }
                    LOGI("=> hardware id from cpuinfo: '%s'\n", hardware_id);
                }
            }
        }
        fclose(fp);
    }

    if (hardware_id[0] != 0) {
        LOGW("\nusing hardware id for device id: '%s'\n", hardware_id);
        strcpy(device_id, hardware_id);
        sanitize_device_id(device_id);
        return;
    }

    strcpy(device_id, "serialno");
    LOGE("=> device id not found, using '%s'\n", device_id);
    return;
}
// End of Device ID functions

void get_twrp_backup_path(const char* sd_path, char *backup_path) {
    char rom_name[PROPERTY_VALUE_MAX] = "noname";
    get_rom_name(rom_name);

    char device_id[PROPERTY_VALUE_MAX];
    get_device_id(device_id);

    time_t t = time(NULL);
    struct tm *timeptr = localtime(&t);
    if (timeptr == NULL) {
        struct timeval tp;
        gettimeofday(&tp, NULL);
        sprintf(backup_path, "%s/%s/%s/%d_%s", sd_path, TWRP_BACKUP_PATH, device_id, tp.tv_sec, rom_name);
    } else {
        char tmp[PATH_MAX];
        strftime(tmp, sizeof(tmp), "%F.%H.%M.%S", timeptr);
        sprintf(backup_path, "%s/%s/%s/%s_%s", sd_path, TWRP_BACKUP_PATH, device_id, tmp, rom_name);
    }
}

void twrp_backup_handler() {
    static char* headers[] = {"选择TWRP备份目录", "", NULL};
    char* list[] = {"备份到内部SD卡",
                        NULL,
                        NULL};

    ui_print_backup_list();

    char *int_sd = "/sdcard";
    char *ext_sd = NULL;
    if (volume_for_path("/emmc") != NULL) {
        int_sd = "/emmc";
        ext_sd = "/sdcard";
    } else if (volume_for_path("/external_sd") != NULL)
        ext_sd = "/external_sd";

    if (ext_sd != NULL)
        list[1] = "备份到外部SD卡";

    int chosen_item = get_menu_selection(headers, list, 0, 0);
    switch (chosen_item)
    {
        case 0:
            {
                if (ensure_path_mounted(int_sd) == 0) {
                    char backup_path[PATH_MAX];
                    get_twrp_backup_path(int_sd, backup_path);
                    twrp_backup(backup_path);
                }
            }
            break;
        case 1:
            {
                if (ensure_path_mounted(ext_sd) == 0) {
                    char backup_path[PATH_MAX];
                    get_twrp_backup_path(ext_sd, backup_path);
                    twrp_backup(backup_path);
                }
            }
            break;
    }
}

void twrp_restore_handler(const char* backup_path) {
    if (ensure_path_mounted(backup_path) != 0) {
        LOGE("Can't mount %s\n", backup_path);
        return;
    }

    static char* headers[] = {  "选择要恢复的备份",
                                NULL
    };

    char tmp[PATH_MAX];
    char device_id[PROPERTY_VALUE_MAX];
    get_device_id(device_id);
    sprintf(tmp, "%s%s/", backup_path, device_id);

    char* file = choose_file_menu(tmp, "", headers);
    if (file == NULL) {
        if (no_files_found)
            ui_print("没有还原文件 %s !\n", tmp);
        return;
    }

    char *backup_source;
    backup_source = dirname(file);
    ui_print("%s 将还原到选定的分区!\n", backup_source);
    sprintf(tmp, "是 - 还原 %s", basename(backup_source));
    if (confirm_selection("从这个备份还原?", tmp))
        twrp_restore(backup_source);
}

static void twrp_backup_restore_menu() {
    static char* headers[] = {  "TWRP备份和还原",
                                "",
                                NULL
    };
    static char* list[] = { "TWRP格式的备份",
                    "从TWRP格式还原",
                    "删除TWRP备份镜像",
                    NULL
    };

    twrp_backup_mode = 1;

    for (;;) {
        int chosen_item = get_filtered_menu_selection(headers, list, 0, 0, sizeof(list) / sizeof(char*));
        if (chosen_item == GO_BACK)
            break;
        switch (chosen_item)
        {
            case 0:
                custom_backup_menu();
                break;
            case 1:
                custom_restore_menu(TWRP_BACKUP_PATH);
                break;
            case 2:
                {
                    char tmp[PATH_MAX];
                    char device_id[PROPERTY_VALUE_MAX];
                    get_device_id(device_id);
                    sprintf(tmp, "%s/%s/", TWRP_BACKUP_PATH, device_id);
                    delete_custom_backups(tmp);
                }
                break;
        }
    }

    twrp_backup_mode = 0;
}

static void regenerate_md5_sum_menu() {
    if (!confirm_selection("这是不推荐!!", "是 - 生成新的MD5校验值"))
        return;

    static char* headers[] = {"重新生成MD5校验值", "选择一个备份文件生成", NULL};

    char* list[] = {"从内部SD卡选择",
                    NULL,
                    NULL};

    char *int_sd = "/sdcard";
    char *ext_sd = NULL;
    if (volume_for_path("/emmc") != NULL) {
        int_sd = "/emmc";
        ext_sd = "/sdcard";
    } else if (volume_for_path("/external_sd") != NULL)
        ext_sd = "/external_sd";

    if (ext_sd != NULL)
        list[1] = "从外部SD卡选择";

    char backup_path[PATH_MAX];
    int chosen_item = get_menu_selection(headers, list, 0, 0);
    switch (chosen_item)
    {
        case 0:
            sprintf(backup_path, "%s", int_sd);
            break;
        case 1:
            sprintf(backup_path, "%s", ext_sd);
            break;
        default:
            return;
    }

    // select backup set and regenerate md5 sum
    strcat(backup_path, "/clockworkmod/backup/");
    if (ensure_path_mounted(backup_path) != 0)
        return;

    char* file = choose_file_menu(backup_path, "", headers);
    if (file == NULL) return;

    char tmp[PATH_MAX];
    char *backup_source;
    backup_source = dirname(file);
    sprintf(tmp, "Process %s", basename(backup_source));
    if (!confirm_selection("重新生成md5校验值?", tmp))
        return;

    ui_print("正在生成MD5校验值...\n");
    // to do (optional): remove recovery.log from md5 sum, but no real need to extra code for this!
    sprintf(tmp, "rm -f '%s/nandroid.md5'; nandroid-md5.sh %s", backup_source, backup_source);
    if (0 != __system(tmp))
        ui_print("生成MD5校验值错误!\n");
    else ui_print("生成MD5校验值成功.\n");
}
//-------- End TWRP Backup and Restore Options


// Custom backup and restore menu
void custom_backup_restore_menu() {
    static char* headers[] = {  "自定义备份与还原",
                                "",
                                NULL
    };

    static char* list[] = { "自定义备份设置",
                    "自定义还原设置",
                    "TWRP备份与还原",
                    "重新生成MD5校验码",
                    "克隆ROM为update.zip",
                    "其他Nandroid设置",
                    NULL
    };

    for (;;) {
        int chosen_item = get_filtered_menu_selection(headers, list, 0, 0, sizeof(list) / sizeof(char*));
        if (chosen_item == GO_BACK)
            break;
        switch (chosen_item)
        {

            case 0:
                custom_backup_menu();
                break;
            case 1:
                custom_restore_menu("clockworkmod/backup");
                break;
            case 2:
                twrp_backup_restore_menu();
                break;
            case 3:
                regenerate_md5_sum_menu();
                break;
            case 4:
#ifdef PHILZ_TOUCH_RECOVERY
                custom_rom_menu();
#endif
                break;
            case 5:
                misc_nandroid_menu();
                break;
        }
    }
}
//-------------- End PhilZ Touch Special Backup and Restore menu and handlers


// launch aromafm.zip from default locations
static int default_aromafm(const char* aromafm_path) {
        if (ensure_path_mounted(aromafm_path) != 0)
            return -1;

        char aroma_file[PATH_MAX];
        sprintf(aroma_file, "%s/clockworkmod/aromafm/aromafm.zip", aromafm_path);
        if (access(aroma_file, F_OK) != -1) {
#ifdef PHILZ_TOUCH_RECOVERY
            force_wait = -1;
#endif
            install_zip(aroma_file);
            return 0;
        }
        return -1;
}

void run_aroma_browser() {
    //we mount volumes so that they can be accessed when in aroma file manager gui
    ensure_path_mounted("/system");
    ensure_path_mounted("/data");
    if (volume_for_path("/sdcard") != NULL)
        ensure_path_mounted("/sdcard");
    if (volume_for_path("/external_sd") != NULL)
        ensure_path_mounted("/external_sd");
    if (volume_for_path("/emmc") != NULL)
        ensure_path_mounted("/emmc");

    int ret = -1;
    if (volume_for_path("/external_sd") != NULL)
        ret = default_aromafm("/external_sd");
    if (ret != 0 && volume_for_path("/sdcard") != NULL)
        ret = default_aromafm("/sdcard");
    if (ret != 0 && volume_for_path("/emmc") != NULL)
        ret = default_aromafm("/emmc");
    if (ret != 0)
        ui_print("No clockworkmod/aromafm/aromafm.zip on sdcards\n");

    // unmount system and data
    ensure_path_unmounted("/system");
    ensure_path_unmounted("/data");
}
//------ end aromafm launcher functions


/***********************************/
/*                                 */
/* Start PhilZ Touch Settings Menu */
/*                                 */
/***********************************/
#ifdef PHILZ_TOUCH_RECOVERY
#include "/root/Desktop/PhilZ_Touch/touch_source/philz_gui_settings.c"
#endif

//start refresh nandroid compression
static void refresh_nandroid_compression() {
    char value[PROPERTY_VALUE_MAX];
    read_config_file(PHILZ_SETTINGS_FILE, "nandroid_compression", value, "false");
    if (strcmp(value, "low") == 0)
        compression_value = TAR_GZ_LOW;
    else if (strcmp(value, "medium") == 0)
        compression_value = TAR_GZ_MEDIUM;
    else if (strcmp(value, "high") == 0)
        compression_value = TAR_GZ_HIGH;
    else
        compression_value = TAR_FORMAT;
}

//start check nandroid preload setting
static void check_nandroid_preload() {
    if (volume_for_path("/preload") == NULL)
        return; // nandroid_add_preload = 0 by default on recovery start

    char value[PROPERTY_VALUE_MAX];
    read_config_file(PHILZ_SETTINGS_FILE, "nandroid_preload", value, "0");
    if (strcmp(value, "true") == 0 || strcmp(value, "1") == 0)
        nandroid_add_preload = 1;
    else
        nandroid_add_preload = 0;
}

//start check nandroid md5 sum
static void check_nandroid_md5sum() {
    char value[PROPERTY_VALUE_MAX];
    read_config_file(PHILZ_SETTINGS_FILE, "nandroid_md5sum", value, "1");
    if (strcmp(value, "false") == 0 || strcmp(value, "0") == 0)
        enable_md5sum = 0;
    else
        enable_md5sum = 1;
}

//start check show nandroid size progress
static void check_show_nand_size_progress() {
    char value_def[3] = "1";
#ifdef BOARD_HAS_SLOW_STORAGE
    sprintf(value_def, "0");
#endif
    char value[PROPERTY_VALUE_MAX];
    read_config_file(PHILZ_SETTINGS_FILE, "show_nandroid_size_progress", value, value_def);
    if (strcmp(value, "false") == 0 || strcmp(value, "0") == 0)
        show_nandroid_size_progress = 0;
    else
        show_nandroid_size_progress = 1;
}

void refresh_recovery_settings() {
    refresh_nandroid_compression();
    check_nandroid_preload();
    check_nandroid_md5sum();
    check_show_nand_size_progress();
#ifdef PHILZ_TOUCH_RECOVERY
    refresh_touch_gui_settings();
#endif
}

//import / export settings
static void import_export_settings() {
    static char* headers[] = {  "保存/还原 设置",
                                "",
                                NULL
    };

    static char* list[] = { "保存设置到SD卡",
                    "还原设置从SD卡",
                    NULL
    };

    for (;;) {
        int chosen_item = get_filtered_menu_selection(headers, list, 0, 0, sizeof(list) / sizeof(char*));
        if (chosen_item == GO_BACK)
            break;
        switch (chosen_item)
        {
            case 0:
                if (copy_a_file(PHILZ_SETTINGS_FILE, PHILZ_SETTINGS_BAK) == 0)
                    ui_print("配置文件备份到 %s\n", PHILZ_SETTINGS_BAK);
                break;
            case 1:
                {
                    static int ret;
                    ret = copy_a_file(PHILZ_SETTINGS_BAK, PHILZ_SETTINGS_FILE);
                    refresh_recovery_settings();
                    if (ret == 0)
                        ui_print("设置加载 %s\n", PHILZ_SETTINGS_BAK);
                }
                break;
        }
    }
}

void show_philz_settings()
{
    static char* headers[] = {  "扩展设置选项",
                                NULL
    };

    static char* list[] = { "打开恢复脚本",
                            "自定义备份和还原",
                            "Aroma文件管理器",
                            "触摸选项设置（禁用）",
                            "保存和还原设置",
                            "重置初始化设置",
                            "关于高级恢复系统",
                             NULL
    };

    for (;;) {
        int chosen_item = get_filtered_menu_selection(headers, list, 0, 0, sizeof(list) / sizeof(char*));
        if (chosen_item == GO_BACK)
            break;
        switch (chosen_item)
        {
            case 0:
                {
                    //search in default ors path
                    choose_default_ors_menu("/sdcard");
                    if (browse_for_file == 0) {
                        //we found .ors scripts in /sdcard default location
                        break;
                    }

                    char *other_sd = NULL;
                    if (volume_for_path("/emmc") != NULL) {
                        other_sd = "/emmc";
                    } else if (volume_for_path("/external_sd") != NULL) {
                        other_sd = "/external_sd";
                    }
                    if (other_sd != NULL) {
                        choose_default_ors_menu(other_sd);
                        //we search for .ors files in second sd under default location
                        if (browse_for_file == 0) {
                            //.ors files found
                            break;
                        }
                    }
                    //no files found in default locations, let's search manually for a custom ors
                    ui_print("在clockworkmod/ors未找到 .ors 文件\n");
                    ui_print("手动搜索 .ors 文件...\n");
                    show_custom_ors_menu();
                }
                break;
            case 1:
                is_custom_backup = 1;
                custom_backup_restore_menu();
                is_custom_backup = 0;
                break;
            case 2:
                run_aroma_browser();
                break;
            case 3:
#ifdef PHILZ_TOUCH_RECOVERY
                show_touch_gui_menu();
#endif
                break;
            case 4:
                import_export_settings();
                break;
            case 5:
                if (confirm_selection("重置所有设置默认值?", "是 - 确定重置")) {
                    delete_a_file(PHILZ_SETTINGS_FILE);
                    refresh_recovery_settings();
                    ui_print("所有设置重置为默认设置!\n");
                }
                break;
            case 6:
                ui_print("支持网站：www.wanjiquan.com 玩机圈\n");
                ui_print("编译机型: " EXPAND(PHILZ_BUILD) " - " EXPAND(TARGET_COMMON_NAME) "\n");
                ui_print("编译版本: " EXPAND(CWM_BASE_VERSION) "\n");
                //ui_print(EXPAND(BUILD_DATE)"\n");
                ui_print("Compiled %s at %s\n", __DATE__, __TIME__);
                break;
        }
    }
}
//---------------- End PhilZ Menu settings and functions
