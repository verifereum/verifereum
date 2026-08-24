Theory vfmTest2371[no_sig_docs]
Ancestors vfmTestDefs2371
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2371_0.nsv", "result2371_1.nsv", "result2371_2.nsv", "result2371_3.nsv", "result2371_4.nsv", "result2371_5.nsv", "result2371_6.nsv", "result2371_7.nsv"];
val thyn = "vfmTestDefs2371";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
