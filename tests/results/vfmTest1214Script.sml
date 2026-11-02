Theory vfmTest1214[no_sig_docs]
Ancestors vfmTestDefs1214
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1214_0.nsv", "result1214_1.nsv", "result1214_2.nsv", "result1214_3.nsv", "result1214_4.nsv", "result1214_5.nsv", "result1214_6.nsv", "result1214_7.nsv", "result1214_8.nsv", "result1214_9.nsv", "result1214_10.nsv", "result1214_11.nsv", "result1214_12.nsv", "result1214_13.nsv", "result1214_14.nsv", "result1214_15.nsv", "result1214_16.nsv"];
val thyn = "vfmTestDefs1214";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
