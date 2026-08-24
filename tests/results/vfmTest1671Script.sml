Theory vfmTest1671[no_sig_docs]
Ancestors vfmTestDefs1671
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1671_0.nsv"];
val thyn = "vfmTestDefs1671";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
