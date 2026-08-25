Theory vfmTest0172[no_sig_docs]
Ancestors vfmTestDefs0172
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0172_0.nsv", "result0172_1.nsv"];
val thyn = "vfmTestDefs0172";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
