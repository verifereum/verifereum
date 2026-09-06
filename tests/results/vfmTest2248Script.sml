Theory vfmTest2248[no_sig_docs]
Ancestors vfmTestDefs2248
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2248_0.nsv", "result2248_1.nsv", "result2248_2.nsv", "result2248_3.nsv", "result2248_4.nsv", "result2248_5.nsv", "result2248_6.nsv", "result2248_7.nsv", "result2248_8.nsv", "result2248_9.nsv", "result2248_10.nsv", "result2248_11.nsv", "result2248_12.nsv", "result2248_13.nsv", "result2248_14.nsv", "result2248_15.nsv", "result2248_16.nsv"];
val thyn = "vfmTestDefs2248";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
