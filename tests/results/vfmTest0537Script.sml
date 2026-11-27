Theory vfmTest0537[no_sig_docs]
Ancestors vfmTestDefs0537
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0537_0.nsv", "result0537_1.nsv", "result0537_2.nsv", "result0537_3.nsv", "result0537_4.nsv", "result0537_5.nsv", "result0537_6.nsv", "result0537_7.nsv"];
val thyn = "vfmTestDefs0537";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
