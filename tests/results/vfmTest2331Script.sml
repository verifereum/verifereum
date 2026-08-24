Theory vfmTest2331[no_sig_docs]
Ancestors vfmTestDefs2331
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2331_0.nsv"];
val thyn = "vfmTestDefs2331";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
