Theory vfmTest0785[no_sig_docs]
Ancestors vfmTestDefs0785
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0785_0.nsv", "result0785_1.nsv"];
val thyn = "vfmTestDefs0785";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
