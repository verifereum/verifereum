Theory vfmTest0278[no_sig_docs]
Ancestors vfmTestDefs0278
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0278_0.nsv", "result0278_1.nsv"];
val thyn = "vfmTestDefs0278";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
