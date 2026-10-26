Theory vfmTest1491[no_sig_docs]
Ancestors vfmTestDefs1491
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1491_0.nsv", "result1491_1.nsv", "result1491_2.nsv", "result1491_3.nsv", "result1491_4.nsv", "result1491_5.nsv", "result1491_6.nsv", "result1491_7.nsv", "result1491_8.nsv", "result1491_9.nsv", "result1491_10.nsv", "result1491_11.nsv", "result1491_12.nsv", "result1491_13.nsv", "result1491_14.nsv", "result1491_15.nsv", "result1491_16.nsv", "result1491_17.nsv", "result1491_18.nsv", "result1491_19.nsv", "result1491_20.nsv", "result1491_21.nsv", "result1491_22.nsv", "result1491_23.nsv", "result1491_24.nsv", "result1491_25.nsv", "result1491_26.nsv", "result1491_27.nsv", "result1491_28.nsv", "result1491_29.nsv", "result1491_30.nsv", "result1491_31.nsv", "result1491_32.nsv", "result1491_33.nsv", "result1491_34.nsv", "result1491_35.nsv"];
val thyn = "vfmTestDefs1491";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
