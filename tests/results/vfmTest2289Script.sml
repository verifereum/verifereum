Theory vfmTest2289[no_sig_docs]
Ancestors vfmTestDefs2289
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2289_0.nsv", "result2289_1.nsv"];
val thyn = "vfmTestDefs2289";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
