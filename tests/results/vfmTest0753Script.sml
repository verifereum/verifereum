Theory vfmTest0753[no_sig_docs]
Ancestors vfmTestDefs0753
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0753_0.nsv", "result0753_1.nsv", "result0753_2.nsv", "result0753_3.nsv", "result0753_4.nsv", "result0753_5.nsv", "result0753_6.nsv", "result0753_7.nsv", "result0753_8.nsv", "result0753_9.nsv", "result0753_10.nsv", "result0753_11.nsv"];
val thyn = "vfmTestDefs0753";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
