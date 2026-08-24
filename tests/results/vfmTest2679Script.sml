Theory vfmTest2679[no_sig_docs]
Ancestors vfmTestDefs2679
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2679_0.nsv", "result2679_1.nsv", "result2679_2.nsv", "result2679_3.nsv"];
val thyn = "vfmTestDefs2679";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
