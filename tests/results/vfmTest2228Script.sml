Theory vfmTest2228[no_sig_docs]
Ancestors vfmTestDefs2228
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2228_0.nsv", "result2228_1.nsv"];
val thyn = "vfmTestDefs2228";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
