Theory vfmTest0618[no_sig_docs]
Ancestors vfmTestDefs0618
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0618_0.nsv", "result0618_1.nsv", "result0618_2.nsv", "result0618_3.nsv"];
val thyn = "vfmTestDefs0618";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
