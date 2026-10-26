Theory vfmTest0060[no_sig_docs]
Ancestors vfmTestDefs0060
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0060_0.nsv", "result0060_1.nsv"];
val thyn = "vfmTestDefs0060";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
