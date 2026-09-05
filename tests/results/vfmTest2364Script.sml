Theory vfmTest2364[no_sig_docs]
Ancestors vfmTestDefs2364
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2364_0.nsv", "result2364_1.nsv", "result2364_2.nsv", "result2364_3.nsv"];
val thyn = "vfmTestDefs2364";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
