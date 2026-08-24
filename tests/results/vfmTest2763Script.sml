Theory vfmTest2763[no_sig_docs]
Ancestors vfmTestDefs2763
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2763_0.nsv", "result2763_1.nsv", "result2763_2.nsv", "result2763_3.nsv"];
val thyn = "vfmTestDefs2763";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
