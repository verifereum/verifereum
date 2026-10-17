Theory vfmTest0748[no_sig_docs]
Ancestors vfmTestDefs0748
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0748_0.nsv", "result0748_1.nsv", "result0748_2.nsv", "result0748_3.nsv", "result0748_4.nsv", "result0748_5.nsv", "result0748_6.nsv", "result0748_7.nsv"];
val thyn = "vfmTestDefs0748";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
