Theory vfmTest2132[no_sig_docs]
Ancestors vfmTestDefs2132
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2132_0.nsv", "result2132_1.nsv", "result2132_2.nsv", "result2132_3.nsv", "result2132_4.nsv", "result2132_5.nsv", "result2132_6.nsv", "result2132_7.nsv", "result2132_8.nsv"];
val thyn = "vfmTestDefs2132";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
