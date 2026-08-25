Theory vfmTest2826[no_sig_docs]
Ancestors vfmTestDefs2826
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2826_0.nsv", "result2826_1.nsv", "result2826_2.nsv", "result2826_3.nsv"];
val thyn = "vfmTestDefs2826";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
