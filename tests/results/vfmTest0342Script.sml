Theory vfmTest0342[no_sig_docs]
Ancestors vfmTestDefs0342
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0342_0.nsv", "result0342_1.nsv", "result0342_2.nsv", "result0342_3.nsv", "result0342_4.nsv", "result0342_5.nsv", "result0342_6.nsv", "result0342_7.nsv", "result0342_8.nsv", "result0342_9.nsv", "result0342_10.nsv", "result0342_11.nsv", "result0342_12.nsv", "result0342_13.nsv", "result0342_14.nsv", "result0342_15.nsv", "result0342_16.nsv", "result0342_17.nsv", "result0342_18.nsv", "result0342_19.nsv", "result0342_20.nsv", "result0342_21.nsv", "result0342_22.nsv", "result0342_23.nsv", "result0342_24.nsv", "result0342_25.nsv", "result0342_26.nsv", "result0342_27.nsv", "result0342_28.nsv", "result0342_29.nsv", "result0342_30.nsv", "result0342_31.nsv"];
val thyn = "vfmTestDefs0342";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
