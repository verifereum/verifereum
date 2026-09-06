Theory vfmTest0306[no_sig_docs]
Ancestors vfmTestDefs0306
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0306_0.nsv", "result0306_1.nsv"];
val thyn = "vfmTestDefs0306";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
