Theory vfmTest1692[no_sig_docs]
Ancestors vfmTestDefs1692
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1692_0.nsv"];
val thyn = "vfmTestDefs1692";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
