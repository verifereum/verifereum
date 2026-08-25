Theory vfmTest1580[no_sig_docs]
Ancestors vfmTestDefs1580
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1580_0.nsv"];
val thyn = "vfmTestDefs1580";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
