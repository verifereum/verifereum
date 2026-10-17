Theory vfmTest2321[no_sig_docs]
Ancestors vfmTestDefs2321
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2321_0.nsv", "result2321_1.nsv", "result2321_2.nsv", "result2321_3.nsv", "result2321_4.nsv", "result2321_5.nsv", "result2321_6.nsv", "result2321_7.nsv", "result2321_8.nsv", "result2321_9.nsv", "result2321_10.nsv", "result2321_11.nsv"];
val thyn = "vfmTestDefs2321";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
