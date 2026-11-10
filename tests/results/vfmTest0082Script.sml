Theory vfmTest0082[no_sig_docs]
Ancestors vfmTestDefs0082
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0082_0.nsv", "result0082_1.nsv", "result0082_2.nsv", "result0082_3.nsv", "result0082_4.nsv"];
val thyn = "vfmTestDefs0082";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
