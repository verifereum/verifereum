Theory vfmTest3037[no_sig_docs]
Ancestors vfmTestDefs3037
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3037_0.nsv", "result3037_1.nsv", "result3037_2.nsv", "result3037_3.nsv"];
val thyn = "vfmTestDefs3037";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
