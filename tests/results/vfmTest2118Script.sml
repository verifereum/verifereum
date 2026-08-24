Theory vfmTest2118[no_sig_docs]
Ancestors vfmTestDefs2118
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2118_0.nsv", "result2118_1.nsv"];
val thyn = "vfmTestDefs2118";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
