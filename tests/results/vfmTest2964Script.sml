Theory vfmTest2964[no_sig_docs]
Ancestors vfmTestDefs2964
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2964_0.nsv", "result2964_1.nsv", "result2964_2.nsv", "result2964_3.nsv", "result2964_4.nsv"];
val thyn = "vfmTestDefs2964";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
