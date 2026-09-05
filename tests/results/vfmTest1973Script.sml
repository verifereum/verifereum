Theory vfmTest1973[no_sig_docs]
Ancestors vfmTestDefs1973
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1973_0.nsv", "result1973_1.nsv"];
val thyn = "vfmTestDefs1973";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
