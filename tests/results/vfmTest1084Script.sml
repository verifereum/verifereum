Theory vfmTest1084[no_sig_docs]
Ancestors vfmTestDefs1084
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1084_0.nsv", "result1084_1.nsv", "result1084_2.nsv", "result1084_3.nsv", "result1084_4.nsv", "result1084_5.nsv", "result1084_6.nsv", "result1084_7.nsv", "result1084_8.nsv", "result1084_9.nsv", "result1084_10.nsv", "result1084_11.nsv", "result1084_12.nsv", "result1084_13.nsv", "result1084_14.nsv", "result1084_15.nsv", "result1084_16.nsv", "result1084_17.nsv", "result1084_18.nsv", "result1084_19.nsv", "result1084_20.nsv", "result1084_21.nsv", "result1084_22.nsv", "result1084_23.nsv", "result1084_24.nsv", "result1084_25.nsv", "result1084_26.nsv", "result1084_27.nsv", "result1084_28.nsv", "result1084_29.nsv", "result1084_30.nsv", "result1084_31.nsv"];
val thyn = "vfmTestDefs1084";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
