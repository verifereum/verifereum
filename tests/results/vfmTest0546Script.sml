Theory vfmTest0546[no_sig_docs]
Ancestors vfmTestDefs0546
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0546_0.nsv", "result0546_1.nsv", "result0546_2.nsv", "result0546_3.nsv", "result0546_4.nsv", "result0546_5.nsv", "result0546_6.nsv", "result0546_7.nsv", "result0546_8.nsv", "result0546_9.nsv", "result0546_10.nsv", "result0546_11.nsv"];
val thyn = "vfmTestDefs0546";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
