Theory vfmTest0642[no_sig_docs]
Ancestors vfmTestDefs0642
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0642_0.nsv", "result0642_1.nsv"];
val thyn = "vfmTestDefs0642";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
