Theory vfmTest2139[no_sig_docs]
Ancestors vfmTestDefs2139
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2139_0.nsv", "result2139_1.nsv", "result2139_2.nsv", "result2139_3.nsv", "result2139_4.nsv", "result2139_5.nsv", "result2139_6.nsv", "result2139_7.nsv", "result2139_8.nsv", "result2139_9.nsv", "result2139_10.nsv", "result2139_11.nsv", "result2139_12.nsv", "result2139_13.nsv", "result2139_14.nsv", "result2139_15.nsv", "result2139_16.nsv"];
val thyn = "vfmTestDefs2139";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
