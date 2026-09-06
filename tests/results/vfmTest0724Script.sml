Theory vfmTest0724[no_sig_docs]
Ancestors vfmTestDefs0724
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0724_0.nsv", "result0724_1.nsv", "result0724_2.nsv", "result0724_3.nsv", "result0724_4.nsv", "result0724_5.nsv", "result0724_6.nsv", "result0724_7.nsv", "result0724_8.nsv", "result0724_9.nsv"];
val thyn = "vfmTestDefs0724";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
