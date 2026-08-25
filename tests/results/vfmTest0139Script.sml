Theory vfmTest0139[no_sig_docs]
Ancestors vfmTestDefs0139
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0139_0.nsv", "result0139_1.nsv", "result0139_2.nsv", "result0139_3.nsv", "result0139_4.nsv", "result0139_5.nsv", "result0139_6.nsv", "result0139_7.nsv", "result0139_8.nsv", "result0139_9.nsv", "result0139_10.nsv", "result0139_11.nsv", "result0139_12.nsv", "result0139_13.nsv", "result0139_14.nsv", "result0139_15.nsv", "result0139_16.nsv", "result0139_17.nsv", "result0139_18.nsv", "result0139_19.nsv", "result0139_20.nsv", "result0139_21.nsv", "result0139_22.nsv", "result0139_23.nsv", "result0139_24.nsv", "result0139_25.nsv", "result0139_26.nsv", "result0139_27.nsv", "result0139_28.nsv", "result0139_29.nsv", "result0139_30.nsv", "result0139_31.nsv"];
val thyn = "vfmTestDefs0139";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
