// 从原始数据中抽取棋局信息
vs.dataToInfo = function(chessData, parseType){
	var replaceQuote = chessData.replace(/\'/g, '"');

	// 标准节点树格式，即鹏飞象棋 PFC 格式
	if (parseType === "auto" && ~replaceQuote.indexOf("n version") || parseType === "pfc") {
		return vs.dataToInfo_PFC(chessData);
	}

	// 东萍象棋 DhtmlXQ 格式
	if (parseType === "auto" && ~replaceQuote.indexOf("[DhtmlXQ") || parseType === "DhtmlXQ") {
		return vs.dataToInfo_DhtmlXQ(chessData);
	}

	// 标准 PGN 格式
	if (parseType === "auto" && ~replaceQuote.indexOf('[Game "Chinese Chess"]') || parseType === "pgn") {
		return vs.dataToInfo_PGN(chessData);
	}

	// 未能识别的数据，返回空
	return {};
};

// 从鹏飞象棋 PFC 格式中抽取棋局信息
vs.dataToInfo_PFC = function(chessData){
	chessData = chessData.replace("<!--", "").replace("-->", "").replace(/<\?xml(.*)\?>/, "");
	chessData = chessData.replace(/<n/ig, "<div").replace(/\/>/ig, "></div>").replace(/<\/n>/ig, "</div>");
	var node  = $($.trim(chessData)), result = {};

	for (var i in vs.info.name) {
		node.attr(i) && (result[i] = node.attr(i));
	}

	return result;
};

// 从标准 PGN 格式中抽取棋局信息
vs.dataToInfo_PGN = function(chessData){
	// 识别模式 A
	var resultA = {}, original = {};
	var lines = chessData.split("\n");

	for (var i = 0; i < lines.length; ++i) {
		var l = $.trim(lines[i]);
		var start = l.    indexOf("[");
		var end   = l.lastIndexOf("]");

		if (~start && ~end) {
			var info  = l.substring(start + 1, end);
			var name  = info.split(/[\s]/)[0];
			var value = $.trim(info.replace(name, ""));
			var quotA = value.charAt(0               ) === "'" || value.charAt(0               ) === '"';
			var quotB = value.charAt(value.length - 1) === "'" || value.charAt(value.length - 1) === '"';
			quotA && (value = value.substring(1                  ));
			quotB && (value = value.substring(0, value.length - 1));
			original[name] = value;
		}
	}

	for (var i in vs.info.name) {
		var name = vs.info.pgn[i] || vs.fieldNameToCamel(i);
		original[name] && (resultA[i] = original[name]);
	}

	// 识别模式 B
	var resultB = {};

	for (var i in vs.info.name) {
		var startTag = "[" + (vs.info.pgn[i] || vs.fieldNameToCamel(i));
		var startPos = chessData.indexOf(startTag);

		if (~startPos) {
			var value = chessData.substring(startPos + startTag.length + 2, chessData.indexOf("]", startPos) - 1);
			value && (resultB[i] = value);
		}
	}

	// AB 结果集合并
	for (var i in resultB) {
		(!resultA[i] || resultB[i].length > resultA[i].length) && (resultA[i] = resultB[i]);
	}

	return resultA;
};

// 从东萍象棋 Dhtml 格式中抽取棋局信息
vs.dataToInfo_DhtmlXQ = function(chessData){
	var result = {};

	for (var i in vs.info.name) {
		var key = "DhtmlXQ_" + (vs.info.DhtmlXQ[i] || i);
		var startTag = "[" + key + "]";
		var startPos = chessData.indexOf(startTag);

		if (~startPos) {
			var value = chessData.substring(startPos + startTag.length, chessData.indexOf("[/" + key + "]", startPos));
			value && (result[i] = value);
		}
	}

	switch (result.result) {
		case "红胜": result.result = "1-0"    ; break;
		case "黑胜": result.result = "0-1"    ; break;
		case "和棋": result.result = "1/2-1/2"; break;
		default    : result.result = "*"      ; break;
	}

	return result;
};
