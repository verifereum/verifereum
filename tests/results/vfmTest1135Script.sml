Theory vfmTest1135[no_sig_docs]
Ancestors vfmTestDefs1135
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1135_0.nsv", "result1135_1.nsv", "result1135_2.nsv", "result1135_3.nsv", "result1135_4.nsv", "result1135_5.nsv", "result1135_6.nsv", "result1135_7.nsv", "result1135_8.nsv", "result1135_9.nsv", "result1135_10.nsv", "result1135_11.nsv", "result1135_12.nsv", "result1135_13.nsv"];
val thyn = "vfmTestDefs1135";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
