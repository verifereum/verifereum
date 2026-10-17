Theory vfmTest0171[no_sig_docs]
Ancestors vfmTestDefs0171
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0171_0.nsv", "result0171_1.nsv", "result0171_2.nsv", "result0171_3.nsv", "result0171_4.nsv", "result0171_5.nsv"];
val thyn = "vfmTestDefs0171";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
