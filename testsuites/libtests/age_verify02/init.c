/* SPDX-License-Identifier: BSD-2-Clause */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <rtems.h>
#include <rtems/test.h>
#include <rtems/test-info.h>
#include <rtems/age_verify.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Fixed reference date to avoid SIS simulator 1988 boot-time issues */
#define CURRENT_YEAR 2026
#define CURRENT_MONTH 3
#define CURRENT_DAY 16

const char rtems_test_name[] = "AGE_VERIFY02";

static void Init(rtems_task_argument arg) {
    char input[32];
    int mm, dd, yyyy;
    int age;
    rtems_age_bracket bracket;
    rtems_status_code sc;
    uint8_t signal;

    (void) arg;

    printf("\n\n*** BEGIN OF TEST %s ***\n", rtems_test_name);
    printf("Interactive Age Verification Provisioning\n\n");

   /* 1. Mock the Input for Headless CI Automation */
    printf("Simulating Date of Birth input for automated testing...\n");
    
    /* Hardcode a 16-year-old user (born in 2009 relative to 2026 reference) */
    strncpy(input, "06/15/2009", sizeof(input) - 1);
    input[sizeof(input) - 1] = '\0';
    
    printf("Mock Input Provided: %s\n", input);

    /* Parse the mock input */
    if (sscanf(input, "%d/%d/%d", &mm, &dd, &yyyy) != 3 &&
        sscanf(input, "%d\\%d\\%d", &mm, &dd, &yyyy) != 3) {
        printf("Invalid mock date format.\n");
        rtems_test_exit(1);
    }

    /* 2. Calculate the Age */
    age = CURRENT_YEAR - yyyy;
    if (CURRENT_MONTH < mm || (CURRENT_MONTH == mm && CURRENT_DAY < dd)) {
        age--;
    }

    /* 3. Map to Statutory Bracket (AB-1043 Compliance) */
    if (age < 13) {
        bracket = AGE_UNDER_13;
    } else if (age >= 13 && age <= 15) {
        bracket = AGE_13_TO_15;
    } else if (age >= 16 && age <= 17) {
        bracket = AGE_16_TO_17;
    } else {
        bracket = AGE_18_PLUS;
    }

    /* 4. Securely Store Bracket */
    sc = rtems_age_set_bracket(bracket);
    if (sc != RTEMS_SUCCESSFUL) {
        printf("FAIL: Could not set bracket. Status: %d\n", sc);
        rtems_test_exit(1);
    }
    
    /* Clear the DOB from local stack memory to prevent leakage */
    mm = dd = yyyy = age = 0;
    memset(input, 0, sizeof(input));
    
    printf("Date of birth securely processed and bracket locked.\n\n");

    /* 5. Retrieve and Verify Signal */
    signal = rtems_age_get_signal();
    printf("Retrieving statutory age signal for 3rd-party application...\n");
    
    switch (signal) {
        case AGE_UNDER_13:
            printf("SIGNAL RECEIVED: AGE_UNDER_13\n");
            printf("-> Action: COPPA limits apply. Telemetry disabled.\n");
            break;
        case AGE_13_TO_15:
            printf("SIGNAL RECEIVED: AGE_13_TO_15\n");
            printf("-> Action: AADC limits apply. High privacy defaults enabled.\n");
            break;
        case AGE_16_TO_17:
            printf("SIGNAL RECEIVED: AGE_16_TO_17\n");
            printf("-> Action: Minor protections apply. Binding EULAs disabled.\n");
            break;
        case AGE_18_PLUS:
            printf("SIGNAL RECEIVED: AGE_18_PLUS\n");
            printf("-> Action: Legal adult. Standard data collection permitted.\n");
            break;
        default:
            printf("SIGNAL RECEIVED: CORRUPT DATA!\n");
            break;
    }

    printf("\n*** END OF TEST %s ***\n\n", rtems_test_name);
    rtems_test_exit(0);
}

/* RTEMS Configuration */
#define CONFIGURE_APPLICATION_NEEDS_CLOCK_DRIVER
#define CONFIGURE_APPLICATION_NEEDS_CONSOLE_DRIVER /* Full console needed for stdin/fgets */
#define CONFIGURE_MAXIMUM_TASKS 1
#define CONFIGURE_INITIAL_EXTENSIONS RTEMS_TEST_INITIAL_EXTENSION
#define CONFIGURE_RTEMS_INIT_TASKS_TABLE
#define CONFIGURE_INIT
#include <rtems/confdefs.h>