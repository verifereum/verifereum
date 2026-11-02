Theory vfmTest3149[no_sig_docs]
Ancestors vfmTestDefs3149
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3149_0.nsv", "result3149_1.nsv", "result3149_2.nsv", "result3149_3.nsv", "result3149_4.nsv", "result3149_5.nsv", "result3149_6.nsv", "result3149_7.nsv"];
val thyn = "vfmTestDefs3149";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
