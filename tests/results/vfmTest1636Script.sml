Theory vfmTest1636[no_sig_docs]
Ancestors vfmTestDefs1636
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1636_0.nsv"];
val thyn = "vfmTestDefs1636";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
