Theory vfmTest3108[no_sig_docs]
Ancestors vfmTestDefs3108
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3108_0.nsv", "result3108_1.nsv"];
val thyn = "vfmTestDefs3108";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
