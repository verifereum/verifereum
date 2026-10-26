Theory vfmTest2938[no_sig_docs]
Ancestors vfmTestDefs2938
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2938_0.nsv", "result2938_1.nsv", "result2938_2.nsv", "result2938_3.nsv", "result2938_4.nsv", "result2938_5.nsv", "result2938_6.nsv", "result2938_7.nsv", "result2938_8.nsv", "result2938_9.nsv", "result2938_10.nsv", "result2938_11.nsv", "result2938_12.nsv", "result2938_13.nsv", "result2938_14.nsv"];
val thyn = "vfmTestDefs2938";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
