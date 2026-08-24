Theory vfmTest2278[no_sig_docs]
Ancestors vfmTestDefs2278
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2278_0.nsv", "result2278_1.nsv"];
val thyn = "vfmTestDefs2278";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
