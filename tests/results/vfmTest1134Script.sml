Theory vfmTest1134[no_sig_docs]
Ancestors vfmTestDefs1134
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1134_0.nsv", "result1134_1.nsv", "result1134_2.nsv", "result1134_3.nsv", "result1134_4.nsv", "result1134_5.nsv", "result1134_6.nsv", "result1134_7.nsv", "result1134_8.nsv", "result1134_9.nsv", "result1134_10.nsv", "result1134_11.nsv", "result1134_12.nsv", "result1134_13.nsv"];
val thyn = "vfmTestDefs1134";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
