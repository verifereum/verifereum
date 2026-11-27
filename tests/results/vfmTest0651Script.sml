Theory vfmTest0651[no_sig_docs]
Ancestors vfmTestDefs0651
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0651_0.nsv", "result0651_1.nsv", "result0651_2.nsv", "result0651_3.nsv", "result0651_4.nsv", "result0651_5.nsv", "result0651_6.nsv", "result0651_7.nsv", "result0651_8.nsv", "result0651_9.nsv", "result0651_10.nsv", "result0651_11.nsv"];
val thyn = "vfmTestDefs0651";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
