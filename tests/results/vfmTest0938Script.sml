Theory vfmTest0938[no_sig_docs]
Ancestors vfmTestDefs0938
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0938_0.nsv", "result0938_1.nsv", "result0938_2.nsv", "result0938_3.nsv"];
val thyn = "vfmTestDefs0938";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
