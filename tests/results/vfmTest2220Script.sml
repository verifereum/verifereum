Theory vfmTest2220[no_sig_docs]
Ancestors vfmTestDefs2220
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2220_0.nsv", "result2220_1.nsv"];
val thyn = "vfmTestDefs2220";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
