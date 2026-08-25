Theory vfmTest0275[no_sig_docs]
Ancestors vfmTestDefs0275
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0275_0.nsv", "result0275_1.nsv", "result0275_2.nsv", "result0275_3.nsv", "result0275_4.nsv", "result0275_5.nsv"];
val thyn = "vfmTestDefs0275";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
