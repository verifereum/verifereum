Theory vfmTest0381[no_sig_docs]
Ancestors vfmTestDefs0381
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0381_0.nsv", "result0381_1.nsv", "result0381_2.nsv", "result0381_3.nsv", "result0381_4.nsv", "result0381_5.nsv", "result0381_6.nsv", "result0381_7.nsv", "result0381_8.nsv", "result0381_9.nsv", "result0381_10.nsv", "result0381_11.nsv", "result0381_12.nsv", "result0381_13.nsv", "result0381_14.nsv", "result0381_15.nsv"];
val thyn = "vfmTestDefs0381";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
