Theory vfmTest0697[no_sig_docs]
Ancestors vfmTestDefs0697
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0697_0.nsv", "result0697_1.nsv", "result0697_2.nsv", "result0697_3.nsv"];
val thyn = "vfmTestDefs0697";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
