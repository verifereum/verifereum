Theory vfmTest0721[no_sig_docs]
Ancestors vfmTestDefs0721
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0721_0.nsv", "result0721_1.nsv", "result0721_2.nsv", "result0721_3.nsv", "result0721_4.nsv", "result0721_5.nsv", "result0721_6.nsv", "result0721_7.nsv", "result0721_8.nsv"];
val thyn = "vfmTestDefs0721";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
