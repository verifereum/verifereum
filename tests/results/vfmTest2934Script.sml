Theory vfmTest2934[no_sig_docs]
Ancestors vfmTestDefs2934
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2934_0.nsv", "result2934_1.nsv", "result2934_2.nsv", "result2934_3.nsv", "result2934_4.nsv", "result2934_5.nsv", "result2934_6.nsv", "result2934_7.nsv", "result2934_8.nsv"];
val thyn = "vfmTestDefs2934";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
