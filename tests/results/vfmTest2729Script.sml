Theory vfmTest2729[no_sig_docs]
Ancestors vfmTestDefs2729
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2729_0.nsv", "result2729_1.nsv", "result2729_2.nsv", "result2729_3.nsv"];
val thyn = "vfmTestDefs2729";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
