Theory vfmTest2333[no_sig_docs]
Ancestors vfmTestDefs2333
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2333_0.nsv", "result2333_1.nsv"];
val thyn = "vfmTestDefs2333";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
