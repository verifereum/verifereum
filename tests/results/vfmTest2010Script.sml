Theory vfmTest2010[no_sig_docs]
Ancestors vfmTestDefs2010
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2010_0.nsv"];
val thyn = "vfmTestDefs2010";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
