Theory vfmTest2687[no_sig_docs]
Ancestors vfmTestDefs2687
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2687_0.nsv", "result2687_1.nsv", "result2687_2.nsv"];
val thyn = "vfmTestDefs2687";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
