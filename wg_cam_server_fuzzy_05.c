#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <getopt.h>  
#include <fcntl.h>  
#include <unistd.h>
#include <errno.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/mman.h>
#include <sys/ioctl.h>
#include <asm/types.h>
#include <time.h>
#include <sys/time.h>
#include <linux/videodev2.h>
#include <linux/fb.h>
#include <libv4l2.h>
#include <libv4l1.h>
//#include "scb_pi_lib.h"
#include <netinet/in.h>    // for sockaddr_in
#include <sys/types.h>    // for socket
#include <sys/socket.h>    // for socket
#include "agv_motor.h"
#include "log.h"
#include "agv_peripheral.h"
#include "time.h"
#include "math.h"
#include "line_fit.h"
#include "wg_net_lib.h"
#include "bsp_RFID_queue.h"
#include "v4l2_video.h"
//extern uint8_t FRAME_RFID_TAG_TYPE,STATION_RFID_TAG_TYPE;

static int time_in_sec_capture = 1000000;

#define CLEAR(x) memset (&(x), 0, sizeof (x))

#define TASKCANCEL      1000
#define PUTDOWNTASK     180
#define HOLDUPTASK      270
#define FIRSTGETPATH    360
#define WRONGWAY        200
#define MISSONSUC       10
#define CHARGE          100
#define FIND_BASKET     2000
#define PB 6
#define PM 5
#define PS 4
#define ZO 3
#define NS 2
#define NM 1
#define NB 0
#define ERRO_GRAD 99
#define ECERRO_GRAD 99

#define ZIHAO

#ifdef ZIHAO
#include "carmotion.h"
#include "pid.h"
#endif
int motion_flag = 0;
int HAVENOT_CHARGE = 0;  //判断是否已经充电
int break_charge_unexpect = 0; //充电是否被意外打断标志位
int card_count = 1; //标记是否为AGV读取的第一张卡号
uint8_t *get_charge_state = NULL; //0:充电桩继电器合上1:充电桩急停2:AGV继电器合上3:充电状态 1正在充电  0充电未连接 
//bit4: AGV光眼接收到信号  1接到 0断开
//bit5: AGV光眼打开状态    1打开 0断开   
//bit6: 通讯的状态  1连上  0断开  
int Turn_rec_angle = 0;        //AGV选择方向角度 
static int Action_rec_angle = 0;    //用于记录在某个站点的动作

char s_rfid_char[5] = "", last_rfid_card[5] = "";//记录地面卡截取后的有用标识位段

double K_line;//图像处理之后的直线斜率值

int rec_speed = 2;//依据标识AGV的运行速度段

int agvstate = 0, taskstate = 4; //AGV的状态及其任务状态标识位

int turn_direction = 1;//方向选择标识位

int left_v = 0, right_v = 0;//

uint8_t *get_rfidm;//读地卡指针

int v_nor4[6] = { 0 }, v_nor3[5] = { 0 }, v_nor2[6] = { 0 }, v_nor[5] = { 0 };//中值滤波暂存位

uint8_t  Error_Type_Pi[6] = { 0, 0, 0, 0, 0, 5 };//向后台发送的错误类型号

static char * dev_name = NULL; //摄像头设备文件索引号
struct timeval tpstart1, tpend1; //系统时间获取

/*
* 顶起
*/
void Hold_Up()
{
	while (Agv_Peripheral_Hold_Up_Goods())
	{
		printf("hold up send success\n");
		usleep(20 * 1000);
	}
	sleep(3);
	while (1){
		printf("judge etric success\n");
		usleep(200 * 1000);
		if (Agv_Peripheral_Get_Etric_State(1) || Agv_Peripheral_Get_Etric_State(2) || Agv_Peripheral_Get_Etric_State(3) || Agv_Peripheral_Get_Etric_State(4))
		{
			printf("dianji1:%d\t dianji2:%d\t dianji3:%d\t dianji4:%d\n", Agv_Peripheral_Get_Etric_State(1), Agv_Peripheral_Get_Etric_State(2), Agv_Peripheral_Get_Etric_State(3), Agv_Peripheral_Get_Etric_State(4));
			if (Agv_Peripheral_Get_Etric_State(1) == 3 || Agv_Peripheral_Get_Etric_State(1) == 4){
				Agv_Peripheral_Set_Bright_Alarm(1);
				Agv_Peripheral_Set_Voice_Alarm(1);
			}
			if (Agv_Peripheral_Get_Etric_State(2) == 3 || Agv_Peripheral_Get_Etric_State(2) == 4){
				Agv_Peripheral_Set_Bright_Alarm(1);
				Agv_Peripheral_Set_Voice_Alarm(1);
			}
			if (Agv_Peripheral_Get_Etric_State(3) == 3 || Agv_Peripheral_Get_Etric_State(3) == 4){
				Agv_Peripheral_Set_Bright_Alarm(1);
				Agv_Peripheral_Set_Voice_Alarm(1);
			}
			if (Agv_Peripheral_Get_Etric_State(4) == 3 || Agv_Peripheral_Get_Etric_State(4) == 4){
				Agv_Peripheral_Set_Bright_Alarm(1);
				Agv_Peripheral_Set_Voice_Alarm(1);
			}

		}
		else
		{
			Agv_Peripheral_Set_Bright_Alarm(0);
			Agv_Peripheral_Set_Voice_Alarm(0);
			break;
		}

	}
}
void Put_Down()
{
	while (Agv_Peripheral_Put_Down_Goods())
		usleep(20 * 1000);
	sleep(2);
	while (1){
		usleep(200 * 1000);
		if (Agv_Peripheral_Get_Etric_State(1) || Agv_Peripheral_Get_Etric_State(2) || Agv_Peripheral_Get_Etric_State(3) || Agv_Peripheral_Get_Etric_State(4))
		{
			printf("dianji1:%d\t dianji2:%d\t dianji3:%d\t dianji4:%d\n", Agv_Peripheral_Get_Etric_State(1), Agv_Peripheral_Get_Etric_State(2), Agv_Peripheral_Get_Etric_State(3), Agv_Peripheral_Get_Etric_State(4));
			if (Agv_Peripheral_Get_Etric_State(1) == 3 || Agv_Peripheral_Get_Etric_State(1) == 4){
				Agv_Peripheral_Set_Bright_Alarm(1);
				Agv_Peripheral_Set_Voice_Alarm(1);
			}
			if (Agv_Peripheral_Get_Etric_State(2) == 3 || Agv_Peripheral_Get_Etric_State(2) == 4){
				Agv_Peripheral_Set_Bright_Alarm(1);
				Agv_Peripheral_Set_Voice_Alarm(1);
			}
			if (Agv_Peripheral_Get_Etric_State(3) == 3 || Agv_Peripheral_Get_Etric_State(3) == 4){
				Agv_Peripheral_Set_Bright_Alarm(1);
				Agv_Peripheral_Set_Voice_Alarm(1);
			}
			if (Agv_Peripheral_Get_Etric_State(4) == 3 || Agv_Peripheral_Get_Etric_State(4) == 4){
				Agv_Peripheral_Set_Bright_Alarm(1);
				Agv_Peripheral_Set_Voice_Alarm(1);
			}
		}
		else
		{

			Agv_Peripheral_Set_Bright_Alarm(0);
			Agv_Peripheral_Set_Voice_Alarm(0);
			break;
		}

	}
}

/**
* 延迟，ms级
*/
void delay(unsigned int howLong)
{
	struct timespec sleeper, dummy;
	sleeper.tv_sec = (time_t)(howLong / 1000);
	sleeper.tv_nsec = (long)(howLong % 1000) * 1000000;
	nanosleep(&sleeper, &dummy);
}



static void errno_exit(const char * s)
{
	fprintf(stderr, "%s error %d, %s\n", s, errno, strerror(errno));
	exit(EXIT_FAILURE);
}


void led_alam(int count)
{

	int i = 0;
	for (i = 0; i < count; i++){
		Agv_Peripheral_Set_LED_State(0);
		Agv_Peripheral_Set_Bright_Alarm(0);
		Agv_Peripheral_Set_Voice_Alarm(0);
		Agv_Peripheral_Set_LED_Bright(0);
		sleep(1);
		Agv_Peripheral_Set_LED_State(1);
		Agv_Peripheral_Set_Bright_Alarm(1);
		Agv_Peripheral_Set_Voice_Alarm(1);
		Agv_Peripheral_Set_LED_Bright(1000);
		sleep(1);
		Agv_Peripheral_Set_LED_State(0);
		Agv_Peripheral_Set_Bright_Alarm(0);
		Agv_Peripheral_Set_Voice_Alarm(0);
		Agv_Peripheral_Set_LED_Bright(0);
	}

}
static int xioctl(int fd, int request, void * arg)
{
	int r;
	do r = ioctl(fd, request, arg);
	while (-1 == r && EINTR == errno);
	return r;
}



void Log_Init(){
	logInit("/home/pi/get_speed.txt");
}


void  stop_car(int *left_v, int *right_v)
{
	int left, right;
	if (*left_v > 0 || *right_v > 0)
	{
		if (*left_v > 10)
			*left_v = *left_v - 10;
		else
			*left_v = 0;
		if (*right_v > 10)
			*right_v = *right_v - 10;
		else
			*right_v = 0;
		AGV_Set_Motor_Speed(MOTOR_LEFT, *left_v);
		AGV_Set_Motor_Speed(MOTOR_RIGHT, *right_v);
		usleep(40 * 1000);

	}


}


void  stop_car_im(int *left_v, int *right_v, int time_ms)
{
	int left, right;
	while (*left_v > 0 || *right_v > 0)
	{
		if (*left_v > 10)
			*left_v = *left_v - 10;
		else
			*left_v = 0;
		if (*right_v > 10)
			*right_v = *right_v - 10;
		else
			*right_v = 0;
		AGV_Set_Motor_Speed(MOTOR_LEFT, *left_v);
		AGV_Set_Motor_Speed(MOTOR_RIGHT, *right_v);
		usleep(time_ms * 1000);

	}
	if (agvstate != 4)
	{
		agvstate = 4;
		sendAgvState(4);
	}


}


//人工暂停的停止
void  stop_car_im_hand(int *left_v, int *right_v, int time_ms)
{
	int left, right;
	while (*left_v > 0 || *right_v > 0)
	{
		if (*left_v > 10)
			*left_v = *left_v - 10;
		else
			*left_v = 0;
		if (*right_v > 10)
			*right_v = *right_v - 10;
		else
			*right_v = 0;
		AGV_Set_Motor_Speed(MOTOR_LEFT, *left_v);
		AGV_Set_Motor_Speed(MOTOR_RIGHT, *right_v);
		usleep(time_ms * 1000);

	}


}


char  Agv_task_code[1000];//存储小车出错的任务编号
int Task_Code_times = 0;//小车走错路的次数

void rfid_motion()
{

	static int HAVENOT_HOULDUP = 0, need_send_flag = 0; //是否已经有物体在顶举标识位，是否需要发送标识位。
	static uint32_t odometer_count = 0, left_odometer_init = 0, right_odometer_init = 0, left_odometer = 0, right_odometer;
	int RFID_COUNT_IN = 0;
	uint8_t Tag_count, Tag_type;
	char tasktype;
	int int_tasktype = 0;
	static int i_down = 1;
	static int hold_action_flag = 0;
	const char *wrong_mes[7] = { "went wrong rfid!",
		"went wrong way!",
		"low power",
		"system error",
		"hardware error",
		"NET_ERRO",
		"EXEC_FAILURE"
	};

	RFID_COUNT_IN = Agv_Peripheral_Get_RFID_Checked_Count();
	printf("***********RFID_COUNT_IN:%d************\n", RFID_COUNT_IN);
	if ((0 != Agv_Peripheral_Get_RFID_Checked_Count()))
	{
		Tag_type = 255;
		get_rfidm = Agv_Peripheral_Get_RFID_tag();
		Tag_type = Rfid_Get_Tag_Type(get_rfidm);
		Tag_count = Rfid_Get_Tag_Count(get_rfidm);
		printf("***********tag_count:%d\t tag_type:%d************\n", Tag_count, Tag_type);
		if ((Tag_type == STATION_RFID_TAG_TYPE)) {
			while (Tag_count) {
				Tag_count--;
				Rfid_Get_Tag(get_rfidm, s_rfid_char, Tag_count);
				Action_rec_angle = getNodeAction(s_rfid_char);        //获取AGV在该站点的动作
				Turn_rec_angle = getNodeDirection(s_rfid_char);       //获取AGV在该站点的转向角
				rec_speed = getNodeSpeed(s_rfid_char);         //获取AGV该站点的速度
				printf("<<<rec_speed:%d>>>>\n", rec_speed);
				if (Action_rec_angle == 100)
				{

					rec_speed = 0;
					Agv_Peripheral_set_lighteye(2); //打开发送光眼
					usleep(20 * 1000);
					Agv_Peripheral_set_lighteye(0); //打开发送光眼
					usleep(20 * 1000);
					Agv_Peripheral_set_reciver(1); //打开光眼的接受端

				}
				if (Action_rec_angle != 200) { //如果卡号是在线路范围内，终止循环

					break;
				}
				if (Tag_count == 0)
					Action_rec_angle = 200; //遍历完线路没有取到站点的动作和速度，站点错误，发送错误信息。
			}
			printf("Action_rec_angle after get:%d\n", Action_rec_angle);
		}
		if (s_rfid_char[0] != 0 && card_count == 1) //如果读取的为第一张卡，上传该站点卡号获取线路
			Action_rec_angle = FIRSTGETPATH;
	}

	switch (Turn_rec_angle)               //依据当前站点的转弯角度，选择速度及转弯方向
	{
	case 30:                    //右转弯
		turn_direction = 2;
		if (rec_speed == 4)
			motion_flag = 2;
		else
			motion_flag = 3;
		Error_Type_Pi[5] = 4;
		break;

	case 0:                      //中间直走
		turn_direction = 1;
		motion_flag = 2;
		Error_Type_Pi[5] = 1;
		break;

	case -30:                       //左转弯
		turn_direction = 0;
		if (rec_speed == 4)
			motion_flag = 2;
		else
			motion_flag = 3;
		Error_Type_Pi[5] = 3;
		break;
	}

	//printf("<<rec_char>>:%s,rec_final_angle:%d,load count:%d,i_down:%d\n",s_rfid_char,Action_rec_angle,AGV_Get_Path_Length(),i_down);
	if (*s_rfid_char != 0)
		strcpy(last_rfid_card, s_rfid_char);

	//后台暂停，后台自动唤醒
	if (isServerSetStop(s_rfid_char) == 1) {
		agvstate = 4;
		sendAgvState(4);
		stop_car_im(&left_v, &right_v, 1);
		printf("<<<>>>%s\n", last_rfid_card);

		Agv_Peripheral_Set_Bright_Alarm(0);
		Agv_Peripheral_Set_Voice_Alarm(0);
		while (isServerSetStop(s_rfid_char)) {
			Error_Type_Pi[4] = 1;
			Agv_Peripheral_Write_Error_Type(Error_Type_Pi);
			printf("server set stop\n");
			usleep(100 * 1000);
			Agv_Peripheral_Set_Bright_Alarm(0);
			Agv_Peripheral_Set_Voice_Alarm(0);
		}
		if (agvstate != 3) {
			agvstate = 3;
			sendAgvState(3);
		}
		Error_Type_Pi[4] = 0;
		Agv_Peripheral_Write_Error_Type(Error_Type_Pi);
	}


	//服务器点击停止，需要特殊处理
	if (isServerSethandStop() == 1) {

		agvstate = 5;         //AGV状态设置为5状态
		sendAgvState(5);
		stop_car_im_hand(&left_v, &right_v, 10);
		printf("<<<>>>%s\n", last_rfid_card);
		while (isServerSethandStop()) {
			Error_Type_Pi[4] = 1;
			Agv_Peripheral_Write_Error_Type(Error_Type_Pi);
			printf("server set stop\n");
			usleep(100 * 1000);
		}
		if (agvstate != 3) {
			agvstate = 3;
			sendAgvState(3);
		}
		Error_Type_Pi[4] = 0;
		Agv_Peripheral_Write_Error_Type(Error_Type_Pi);
	}

	// 1 入库任务 2 出库任务 3 空车返程 4 自动充电 5 人工控制 6 空车调配 7 空框调配 8 空框返程 9获取空框
	//依据不同的任务类型及线路位置更改不同的radar检测距离
	if (Get_AGV_TaskType() == '1')
		int_tasktype = 1;
	if (Get_AGV_TaskType() == '2')
		int_tasktype = 2;
	if (Get_AGV_TaskType() == '3')
		int_tasktype = 3;
	if (Get_AGV_TaskType() == '4')
		int_tasktype = 4;
	if (Get_AGV_TaskType() == '5')
		int_tasktype = 5;
	if (Get_AGV_TaskType() == '6')
		int_tasktype = 6;
	if (Get_AGV_TaskType() == '7')
		int_tasktype = 7;
	if (Get_AGV_TaskType() == '8')
		int_tasktype = 8;
	if (Get_AGV_TaskType() == '9')
		int_tasktype = 9;
	switch (int_tasktype) {

	case 1:                   //入库任务
		if ((HAVENOT_HOULDUP == 1) || (hold_action_flag == 1)) {    //如果需要顶起但是还未顶起 车身模式为2
			Action_rec_angle = HOLDUPTASK;
			agv_pidmotor_set_in(1);
			printf("mode_2");
		}
		if (need_send_flag == 1) {
			left_odometer_init = AGV_Get_Motor_Odometer();
			if (left_odometer == 0) {
				odometer_count = 0;
			}
			else {

				printf("left_odometer:%d\n", left_odometer);
				odometer_count += (left_odometer_init - left_odometer);
			}
			left_odometer = left_odometer_init;
			printf("odometer_count:%d\n", odometer_count);
			printf("AGV_Get_left_Motor_Odometer_init:%d\n", left_odometer_init);
			if (odometer_count > 80) {

				agv_pidmotor_set_in(0);
				printf("mode_1");
				if (taskstate != 3) {
					sendTaskState(3);
					taskstate = 3;
					printf("<<<<<<already task start!>>>>>\n");
				}
				left_odometer = 0;
				odometer_count = 0;
				need_send_flag = 0;
			}
		}
		break;
	case 2:   //出库任务

		if ((AGV_Get_Remaining_Length() == 2) || (AGV_Get_Remaining_Length() == 1) || (HAVENOT_HOULDUP == 1) || (hold_action_flag == 1)) {
			agv_pidmotor_set_in(1);
			printf("mode_2");
		}
		else {
			agv_pidmotor_set_in(0);
			printf("mode_1");
		}
		if ((HAVENOT_HOULDUP == 1) || (hold_action_flag == 1)) {
			Action_rec_angle = HOLDUPTASK;
		}
		break;
	case 3: //空车返程
		if ((AGV_Get_Remaining_Length() == 2) || (AGV_Get_Remaining_Length() == 1)) {
			agv_pidmotor_set_in(1);
			printf("mode_2");
		}
		else {
			agv_pidmotor_set_in(0);
			printf("mode_1");
		}
		break;
	case 4:  //4 自动充电

		if ((AGV_Get_Remaining_Length() == 2) || (AGV_Get_Remaining_Length() == 1)) {
			agv_pidmotor_set_in(1);
			printf("mode_2");

		}
		else {
			agv_pidmotor_set_in(0);
			printf("mode_1");
		}
		break;

		break;
	case 5: //5 人工控制
		agv_pidmotor_set_in(1);
		printf("mode_2");
		break;
	case 6:   //6 空车调配
		if ((AGV_Get_Remaining_Length() == 2) || (AGV_Get_Remaining_Length() == 1)) {
			agv_pidmotor_set_in(1);
			printf("mode_2");
		}
		else {
			agv_pidmotor_set_in(0);
			printf("mode_1");
		}
		break;


	case 7: //7 空框调配
		if ((HAVENOT_HOULDUP == 1) || (hold_action_flag == 1)) {
			Action_rec_angle = HOLDUPTASK;
			agv_pidmotor_set_in(1);
			printf("mode_2");
		}
		else {
			agv_pidmotor_set_in(0);
			printf("mode_1");
		}
		break;

	case 8:  //8 空框返程
		if ((HAVENOT_HOULDUP == 1) || (hold_action_flag == 1)) {
			Action_rec_angle = HOLDUPTASK;
			agv_pidmotor_set_in(1);
			printf("mode_2");
		}
		else {
			agv_pidmotor_set_in(0);
			printf("mode_1");
		}
		break;
	case 9:  //9获取空框
		if (AGV_Get_Present_Nid() == 0) {
			agv_pidmotor_set_in(1);
			printf("mode_2");
		}
		else {
			agv_pidmotor_set_in(0);
			printf("mode_1");
		}
		if ((HAVENOT_HOULDUP == 1) || (hold_action_flag == 1)) {
			Action_rec_angle = HOLDUPTASK;
		}
		break;

	}


	if (isTaskCancal()) {
		Action_rec_angle = TASKCANCEL;
		printf("taskcancel good \n");
	}

	switch (Action_rec_angle) {


	case CHARGE:                    //自动充电任务
		printf("<<<rec_speed:%d>>>>\n", rec_speed);
		get_charge_state = Agv_Peripheral_Get_Charging_state();
		printf("\nin charge mode 1");
		printf("3@ %d\t  5@%d\t4@ %d\t  6@%d\t", get_charge_state[3], get_charge_state[5], get_charge_state[4], get_charge_state[6]);

		HAVENOT_CHARGE = 1;
		if (get_charge_state[4])
		{

			while (resetPathCount());
			stop_car_im(&left_v, &right_v, 1);
			printf("wait for 5 sec\n");
			Agv_Peripheral_set_reciver(0);  //关闭接收光眼
			Agv_Peripheral_set_lighteye(1); //打开发送光眼
			get_charge_state = Agv_Peripheral_Get_Charging_state();
			sleep(15);
			if (get_charge_state[6])                 //10s后有充电正常信号
			{

				printf("\n\n in charge mode 3 charging !!!!!!!\n");

				while (get_charge_state[6])          //充电信号是否持续
				{
					break_charge_unexpect = 1;      //只要被意外打断 不能进入循环执行

					if (isTaskCancal())        //被后台强制唤醒执行任务
					{
						break_charge_unexpect = 0;    //被调度系统打断 非意外打断
						Agv_Peripheral_set_lighteye(0); //将发送光眼关闭
						HAVENOT_CHARGE = 0;
						if (taskstate != 5) {
							sendTaskState(5);
							taskstate = 5;
							while (resetPathCount());
							printf("<<<<<<already task end end!>>>>>\n");
						}
						printf("taskcancel and get path;\n");
						while ((AGV_Get_Path_Length() == 0) || (AGV_Get_Path_Length() == 1)) {
							printf(">>>>waitfor the the new task chongdian>>>>\n ");
							card_count++;
							usleep(20 * 1000);
						}
						if (taskstate != 3) {
							sendTaskState(3);
							taskstate = 3;
							printf("<<<<<<already task start!>>>>>\n");
						}
						Action_rec_angle = GetLastAction();
						rec_speed = 2;
						motion_flag = 2;
						break;
					}


					if (Agv_Peripheral_Get_VOL_NUM() >= 99)          //如果电压达到充满额定值，电量达到100
					{
						break_charge_unexpect = 0;
						Agv_Peripheral_set_lighteye(0);
						HAVENOT_CHARGE = 0;

						printf("connect error  waitfor moving\n");
						sleep(5);

						sendTaskState(4);
						taskstate = 4;
						while (resetPathCount());
						printf("waiting for path to mission");
						do {
							usleep(10 * 1000);
							printf(">>>>waitfor the the new task chongdian1>>>>\n ");
						} while ((AGV_Get_Path_Length() == 0));  //停止等待线路

						if (taskstate != 3) {
							sendTaskState(3);
							taskstate = 3;
							printf("<<<<<<already task start!>>>>>\n");
						}
						Action_rec_angle = GetLastAction();
						rec_speed = 2;
						motion_flag = 2;

						break;

					}


					sleep(1);
				}
				if (break_charge_unexpect)   //充电被意外停止，离开
				{
					Agv_Peripheral_set_lighteye(0);      //将发送光眼关闭
					printf("connect error  waitfor moving\n");
					sleep(2);      //停止两秒等待充电桩缩回
					rec_speed = 2;
				}

			}
			else{
				Agv_Peripheral_set_lighteye(0);          //第一次没有通讯成功，关闭发送光眼

				printf("<<<<<<<<<<<<<<<<<<<<<<<<<<<can not connect one>>>>>>>>>>>>>>>>>>>");
				rec_speed = 2;

			}

		}
		break;







	case TASKCANCEL:                                      //任务取消
		stop_car_im(&left_v, &right_v, 1);
		if (taskstate != 5) {
			while (resetPathCount());
			sendTaskState(5);
			taskstate = 5;

			printf("<<<<<<already task end end!>>>>>\n");
		}
		printf("taskcancel and get path;\n");
		while ((AGV_Get_Path_Length() == 0) || (AGV_Get_Path_Length() == 1)) {
			card_count++;
			printf(">>>>waitfor the the new task TASKCANCEL>>>>\n ");

			usleep(20 * 1000);
		}
		if (taskstate != 3) {
			sendTaskState(3);
			taskstate = 3;
			printf("<<<<<<already task start!>>>>>\n");
		}
		Action_rec_angle = GetLastAction();
		//rec_speed=GetLastSpeed();
		motion_flag = 2;
		break;

	case PUTDOWNTASK:                  //到点放下货物

		if (i_down == 0) {
			tasktype = Get_AGV_TaskType();        //得到任务类型，如果是出库任务，出库任务结束处AGV不执行放下动作
			while (resetPathCount());
			stop_car_im(&left_v, &right_v, 1);
			if (taskstate != 4) {
				sendTaskState(4);
				taskstate = 4;
				printf("<<<<<<already task end!>>>>>\n");
			}
			if (tasktype != '2') {
				Put_Down();
				i_down = 1;
			}
			printf("put down1 and get path;\n");
			while (AGV_Get_Path_Length() == 0) {
				printf(">>>>waitfor the the new task PUTDOWNTASK>>>>\n ");
				usleep(20 * 1000);
			}
			updateAgvPlace(last_rfid_card);

			if (Action_rec_angle != HOLDUPTASK) {
				printf("<<\ngetnowindex6:%d\n>>", getNodeIndex(s_rfid_char));
				if (taskstate != 3) {
					sendTaskState(3);
					taskstate = 3;
					printf("<<<<<<already task start!>>>>>\n");
					//usleep(20*1000);
				}
			}
			Agv_Peripheral_Set_Zero_Flag();
			while (Agv_Peripheral_Get_Zero_Flag()) {
				printf("clearing the rfid buffer...");
				usleep(200 * 1000);
			}

			motion_flag = 2;

		}
		break;


	case HOLDUPTASK:                   //到点顶起货物
		printf("\ni_down%d\n", i_down);
		if (i_down > 0) {
			HAVENOT_HOULDUP = 1;

			if (Agv_Peripheral_Get_Magne_Switch_State()) {

				odometer_count = 0;
				left_odometer = 0;
				stop_car_im(&left_v, &right_v, 5);

				while (Agv_Peripheral_Hold_Up_Goods())
					usleep(10 * 1000);
				//sleep(1);
				Agv_Peripheral_Set_Zero_Flag();          //让AGV重新读卡
				while (Agv_Peripheral_Get_Zero_Flag()) {
					printf("clearing the rfid buffer...");
					usleep(200 * 1000);
				}
				Hold_Up();
				updateAgvPlace(last_rfid_card);
				need_send_flag = 1;
				printf("good need flag");
				//rec_speed=2;
				HAVENOT_HOULDUP = 0;
				hold_action_flag = 0;
				while (1) {
					Action_rec_angle = getNodeAction(s_rfid_char);
					rec_speed = getNodeSpeed(s_rfid_char);

					printf("\n<<<rec_speed IN HOLD:%d>>>>\n", rec_speed);
					if (Action_rec_angle != 200) {                  //如果卡号是在线路范围内，终止循环
						break;
					}
				}

				i_down = 0;
			}
			else {

				rec_speed = 0;
				left_odometer_init = AGV_Get_Motor_Odometer();
				if (left_odometer == 0) {
					odometer_count = 0;
				}
				else {

					printf("left_odometer:%d\n", left_odometer);
					odometer_count += (left_odometer_init - left_odometer);
				}
				left_odometer = left_odometer_init;
				printf("odometer_count:%d\n", odometer_count);
				printf("AGV_Get_left_Motor_Odometer_init:%d\n", left_odometer_init);
				if (odometer_count > 50) {

					//sleep(10);
					odometer_count = 0;
					left_odometer = 0;
					while (resetPathCount());
					taskstate = 4;

					printf("AGV PATH:%d\n", AGV_Get_Path_Length());
					stop_car_im(&left_v, &right_v, 1);
					/*Agv_Peripheral_Set_Zero_Flag();
					while(Agv_Peripheral_Get_Zero_Flag()){
					printf("clearing the rfid buffer...");
					usleep(200*1000);
					}*/
					updateAgvPlace(s_rfid_char);
					usleep(20 * 1000);
					sendErrorMessage(7, wrong_mes[6]);
					printf("wrong card and get path;\n");
					while (AGV_Get_Path_Length() == 0) {
						printf(">>>>waitfor the the new task HOLDUPTASK>>>>\n ");
						usleep(20 * 1000);
					}

					sendTaskState(3);
					taskstate = 3;


					HAVENOT_HOULDUP = 0;
					hold_action_flag = 0;
					Action_rec_angle = GetLastAction();
					//rec_speed=GetLastSpeed();
					rec_speed = getNodeSpeed(s_rfid_char);
					printf("\nerro card get angle:%d\n", Action_rec_angle);
					//sleep(10);
					motion_flag = 2;
				}
			}


		}
		motion_flag = 3;
		break;


	case FIRSTGETPATH:                                   //第一次读到卡取得路线

		while (resetPathCount());
		stop_car_im(&left_v, &right_v, 5);
		if (agvstate != 1) {
			updateAgvPlace(s_rfid_char);          //发送第一张读到的rfid卡
			sleep(1);
			sendAgvState(1);                      //刚开机状态，向服务器发送agv状态1,待就绪
			agvstate = 1;
			printf(">>>>>>>>>>>>>>>>>>>>agvstat:%d\n", agvstate);
		}
		printf("stop in first card and get path;\n");
		while (AGV_Get_Path_Length() == 0) {
			card_count++;
			printf(">>>>waitfor the the new task FIRSTGETPATH>>>>\n ");
			usleep(20 * 1000);
		}
		if (taskstate != 3) {
			sendTaskState(3);
			taskstate = 3;
		}
		Action_rec_angle = getNodeAction(s_rfid_char);
		motion_flag = 2;
		break;

	case WRONGWAY:                                   //读错卡了
		stop_car_im(&left_v, &right_v, 1);
		while (resetPathCount());
		taskstate = 4;

		printf("AGV PATH:%d\n", AGV_Get_Path_Length());
		updateAgvPlace(s_rfid_char);
		usleep(20 * 1000);
		if (HAVENOT_CHARGE != 1)
			sendErrorMessage(1, wrong_mes[0]);
		else
			sendErrorMessage(7, wrong_mes[6]);   //充电任务执行失败
		printf("wrong card and get path;\n");
		Agv_Peripheral_Set_Zero_Flag();
		while (Agv_Peripheral_Get_Zero_Flag()) {
			printf("clearing the rfid buffer...");
			usleep(200 * 1000);
		}
		while ((AGV_Get_Path_Length() == 0) || (AGV_Get_Path_Length() == 1)) {
			printf(">>>>waitfor the the new task WRONGWAY>>>>\n ");
			usleep(20 * 1000);
		}
		if (taskstate != 3) {
			sendTaskState(3);
			taskstate = 3;
			printf("<<<<<<already task start!>>>>>\n");
		}
		Action_rec_angle = GetLastAction();
		printf("\nerro card get angle:%d\n", Action_rec_angle);
		//rec_speed=2;
		motion_flag = 2;
		break;

	case MISSONSUC:                       //成功返回  对应于逻辑停止
		stop_car_im(&left_v, &right_v, 1);
		while (resetPathCount())
			;
		sendTaskState(4);
		taskstate = 4;

		printf("waiting for path to mission");
		do {
			usleep(10 * 1000);
			printf(">>>>waitfor the the new task MISSONSUC>>>>\n ");
		} while ((AGV_Get_Path_Length() == 0));  //停止等待线路
		if (AGV_action() == 2) {   //如果接收到的是第一个点需要顶举任务 如 1 入库任务 2 出库任务 7 空框调配 8 空框返程 9获取空框 强制跳转到顶举动作

			hold_action_flag = 1;     //此标志位对应于强制跳转到顶举任务
			need_send_flag = 1;        //对流水线处的AGV发送做特殊处理，延迟到走动80cm后再发送任务启动。确保车子已经离开流水线
			Action_rec_angle = HOLDUPTASK;
			printf("hold_action_flag:%d\n", hold_action_flag);
			if (agvstate != 3) {
				agvstate = 3;
				sendAgvState(3);
			}
			if (Get_AGV_TaskType() != '1')      //%%%%%如果是入库任务此处不可以直接启动任务，启动任务流水线会出现错误。
			{
				if (taskstate != 3) {
					sendTaskState(3);
					taskstate = 3;
					printf("<<<<<<already task start!>>>>>\n");
				}
			}
		}
		if (Action_rec_angle != HOLDUPTASK) {                 //如果停止后接收到的是 空车返程及空框调配任务 直接向后台发送启动任务及启动AGV
			Action_rec_angle = getNodeAction(s_rfid_char);
			if (agvstate != 3) {
				agvstate = 3;
				sendAgvState(3);
			}
			if (taskstate != 3) {
				sendTaskState(3);
				taskstate = 3;
				printf("<<<<<<already task start!>>>>>\n");
			}

		}
		motion_flag = 3;
		break; //add by cgd
	default:
		motion_flag = 2;

	}


}

//图像处理主要程序
static void run()
{

	static int v_scbrob, last_vscb = 0, find_count = 0, mis_count = 50;
	static int slow_down = 0;
	int temp;
	double timeuse1, timeuse1_all = 0.0;
	unsigned int count;
	long int frames;
	int get_value = 0, get_value1 = 0, get_value2 = 0;
	int sum_rec_vwg;
	frames = 0;

	double *V_control;
	while (1) {

		while (Agv_Peripheral_Get_Screen_State()){
			printf("enter sys test!");//判断是否进入调试状态
			usleep(20 * 1000);
		}
		gettimeofday(&tpstart1, NULL);


		//printf("%%%%%%%%%        v_scbrob_control>>>>>>>>>>%d     %%%%%%%%%%%%\n",v_scbrob);	
		//timeuse1_all>30*1000
		if (v4l2_Get_flag()){

			V_control = v4l2_video_Get_BUFF_tag(turn_direction);
			//printf("*****%f\n",*V_control);
			v_scbrob = (int)V_control[1];
			K_line = V_control[0];
			printf("<<<<<<<<    v_scbrob:%d      kkkkkkk_line:%f     >>>>>>>>>\n", v_scbrob, K_line);

			if (v_scbrob <= 0){
				v_scbrob = -1;
			}
			else
				//if(v_scbrob!=last_vscb)
			{
#ifndef	ZIHAO
				v_nor4[5] = v_scbrob;//对当前十行进行三个点中值滤波
				for (i = 0; i < 5; i++)
					v_nor4[i] = v_nor4[i + 1];
				for (i = 0; i < 5; i++)
					v_nor3[i] = v_nor4[i];
				for (j = 0; j < 4; j++)
				{
					for (i = 0; i<4 - j; i++)
					if (v_nor3[i]>v_nor3[i + 1])
					{
						temp = v_nor3[i];
						v_nor3[i] = v_nor3[i + 1];
						v_nor3[i + 1] = temp;
					}
				}                  //中值滤波结束
				last_vscb = v_scbrob;
				v_scbrob = v_nor3[2];
#endif
			}

#ifndef ZIHAO			
			if (v_scbrob != -1)
			{
				mis_count = 50;
				find_count++;
				if (find_count > 15)
				{
					find_count = 21;
					slow_down = 0;
				}
			}
			else
			{
				find_count = 0;
				mis_count--;
			}
			if (mis_count < 0)
			{
				slow_down = 1;//连续十帧监测不到图像，停止
			}

			if (slow_down == 1){
				v_scbrob = 0;	 //数据为零代表出错
			}

			for (i = 0; i < 6; i++)
				printf("%d\t", Error_Type_Pi[i]);
			printf("\n");
#endif
			Agv_Peripheral_Write_Error_Type(Error_Type_Pi);
			rfid_motion(); //进行读卡判断
			carmotion(v_scbrob, K_line, &motion_flag, rec_speed);

#ifndef ZIHAO			
			if (v_scbrob >= 0){

				timeuse1_all = 0.0;
#ifdef	ZIHAO
				carmotion(v_scbrob, K_line, &motion_flag, rec_speed);
#else
				car_motion(v_scbrob, K_line);//电机控制
#endif
			}
			else
			{
				timeuse1_all = 0.0;
				for (i = 0; i < 6; i++)
				{
					sum_rec_vwg += v_nor4[i];

				}
				sum_rec_vwg = sum_rec_vwg / 6;
#ifdef	ZIHAO
				carmotion(sum_rec_vwg, K_line, &motion_flag, rec_speed);
#else
				car_motion(sum_rec_vwg, K_line);//电机控制
#endif					

			}
#endif			

			gettimeofday(&tpend1, NULL);
			timeuse1 = 1000 * 1000 * (tpend1.tv_sec - tpstart1.tv_sec) + tpend1.tv_usec - tpstart1.tv_usec;
			timeuse1_all += timeuse1;
			if (timeuse1 > 10 * 1000){
				//printf("\n\n\n %f  >>>>> car_motion >> \n",timeuse1);
				//sleep(5);

			}


			while (v4l2_Reset_flag())
			{
				usleep(1000);
			}
		}

	}
}

static const char short_options[] = "d:ht:";
static const struct option long_options[] = {
	{ "device", required_argument, NULL, 'd' },
	{ "help", no_argument, NULL, 'h' },
	{ "time", no_argument, NULL, 't' },
	{ 0, 0, 0, 0 }
};

int main(int argc, char ** argv)
{
	int i = 0;
	Log_Init();
#ifdef ZIHAO
	printf("ZIHAO_PID_INIT");
	pid_init();
#endif
	printf("Log_Init\n");
	AGV_Motor_Init();
	printf("AGV_Motor_Init\n");
	Agv_Peripheral_Init();
	listenRemoteMsg();
	printf("Agv_Peripheral_Init\n");
	Agv_Login("00000");
	//while(isconnetnet());

	sendAgvState(0);
	agvstate = 0;
	taskstate = 0;
	Agv_Peripheral_Set_Net_initialization(1);

	v4l2_video_Init(argc, argv);//摄像头初始化

	printf("v4l2_video_Init\n");
	agvstate = 0;
	//mis_count=0;

	dev_name = "/dev/video0";
	Agv_Peripheral_Set_Video_initialization(1);

	Agv_Peripheral_Set_Bright_Alarm(0);

	Put_Down();
	printf("Put_Down\n");
	//Hold_Up();
	printf("Hold_Up\n");

	memset(s_rfid_char, 0, sizeof(s_rfid_char));

	for (i = 0; i++; i < 5)
		Error_Type_Pi[i] = 0;
	Error_Type_Pi[5] = 1;
	Agv_Peripheral_Write_Error_Type(Error_Type_Pi);
	for (i = 0; i < 6; i++)
		printf("%d\t", Error_Type_Pi[i]);
	printf("\n");


	printf("led_alam\n");
	led_alam(2);//开机灯闪烁两次代表开机完成


	Agv_Peripheral_Set_System_initialization(1);

	agv_pidmotor_set_in(1);   //设置激光雷达初始状态
	Agv_Peripheral_set_reciver(0);
	Agv_Peripheral_set_lighteye(2);
	usleep(10 * 1000);
	Agv_Peripheral_set_lighteye(0); //打开发送光眼


	run();
	printf("《《《end the program》》》\n");
	AGV_Close_Motor_Uart();
	Agv_Peripheral_Spi_Close();
	v4l2_video_close();
	return 0;
}
